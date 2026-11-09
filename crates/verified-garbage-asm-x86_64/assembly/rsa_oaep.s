// The functions of `src/rsa_oaep.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_oaep_decrypt_crt_ifma:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked_ifma}
	mov r11, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+280], r11
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+32]
	cmp r11, 16
	je 20f
	cmp r11, 20
	je 22f
	cmp r11, 28
	je 24f
	cmp r11, 32
	je 26f
	cmp r11, 48
	je 28f
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 130
	jb 210f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 64
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 65
	mov r9, QWORD PTR [rsp+184]
	sub r9, 65
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
212:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 213f
	jmp 214f
213:
	mov r10, rax
214:
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 215b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 212b
	mov rax, QWORD PTR [rsp+112]
	add rax, 65
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 64
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
216:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 217f
	jmp 218f
217:
	mov r10, rax
218:
	mov r8d, 0
219:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 219b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 216b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
220:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 64
	jne 220b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 129
	mov r10, QWORD PTR [rsp+184]
	sub r10, 129
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
221:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 221b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 129
	mov r10, QWORD PTR [rsp+184]
	sub r10, 129
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
222:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 222b
	mov r8d, 0
223:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 223b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
224:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
225:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 225b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 224b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
226:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 226b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 130
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 211f
210:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
227:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 227b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
211:
	jmp 29f
28:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 98
	jb 228f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 48
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 49
	mov r9, QWORD PTR [rsp+184]
	sub r9, 49
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
230:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 231f
	jmp 232f
231:
	mov r10, rax
232:
	mov r8d, 0
233:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 233b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 230b
	mov rax, QWORD PTR [rsp+112]
	add rax, 49
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 49
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 48
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
234:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 235f
	jmp 236f
235:
	mov r10, rax
236:
	mov r8d, 0
237:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 237b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 234b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 49
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
238:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 48
	jne 238b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 97
	mov r10, QWORD PTR [rsp+184]
	sub r10, 97
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
239:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 239b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 97
	mov r10, QWORD PTR [rsp+184]
	sub r10, 97
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
240:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 240b
	mov r8d, 0
241:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 241b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
242:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
243:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 243b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 242b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
244:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 244b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 98
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 229f
228:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
245:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 245b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
229:
29:
	jmp 27f
26:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 246f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
248:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 249f
	jmp 250f
249:
	mov r10, rax
250:
	mov r8d, 0
251:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 251b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 248b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
252:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 253f
	jmp 254f
253:
	mov r10, rax
254:
	mov r8d, 0
255:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 255b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 252b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
256:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 256b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
257:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 257b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
258:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 258b
	mov r8d, 0
259:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 259b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
260:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
261:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 261b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 260b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
262:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 262b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 247f
246:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
263:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 263b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
247:
27:
	jmp 25f
24:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 58
	jb 264f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 28
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 29
	mov r9, QWORD PTR [rsp+184]
	sub r9, 29
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
266:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 267f
	jmp 268f
267:
	mov r10, rax
268:
	mov r8d, 0
269:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 269b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 266b
	mov rax, QWORD PTR [rsp+112]
	add rax, 29
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 29
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 28
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
270:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 271f
	jmp 272f
271:
	mov r10, rax
272:
	mov r8d, 0
273:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 273b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 270b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 29
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
274:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 28
	jne 274b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 57
	mov r10, QWORD PTR [rsp+184]
	sub r10, 57
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
275:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 275b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 57
	mov r10, QWORD PTR [rsp+184]
	sub r10, 57
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
276:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 276b
	mov r8d, 0
277:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 277b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
278:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
279:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 279b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 278b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
280:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 280b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 58
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 265f
264:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
281:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 281b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
265:
25:
	jmp 23f
22:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 42
	jb 282f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 20
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 21
	mov r9, QWORD PTR [rsp+184]
	sub r9, 21
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
284:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 285f
	jmp 286f
285:
	mov r10, rax
286:
	mov r8d, 0
287:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 287b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 284b
	mov rax, QWORD PTR [rsp+112]
	add rax, 21
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 21
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 20
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
288:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 289f
	jmp 290f
289:
	mov r10, rax
290:
	mov r8d, 0
291:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 291b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 288b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 21
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
292:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 20
	jne 292b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 41
	mov r10, QWORD PTR [rsp+184]
	sub r10, 41
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
293:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 293b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 41
	mov r10, QWORD PTR [rsp+184]
	sub r10, 41
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
294:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 294b
	mov r8d, 0
295:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 295b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
296:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
297:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 297b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 296b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
298:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 298b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 42
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 283f
282:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
299:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 299b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
283:
23:
	jmp 21f
20:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 34
	jb 2100f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 16
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 17
	mov r9, QWORD PTR [rsp+184]
	sub r9, 17
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2102:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2103f
	jmp 2104f
2103:
	mov r10, rax
2104:
	mov r8d, 0
2105:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2105b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2102b
	mov rax, QWORD PTR [rsp+112]
	add rax, 17
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 17
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 16
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2106:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2107f
	jmp 2108f
2107:
	mov r10, rax
2108:
	mov r8d, 0
2109:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2109b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2106b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 17
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
2110:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 16
	jne 2110b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov r10, QWORD PTR [rsp+184]
	sub r10, 33
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
2111:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 2111b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 33
	mov r10, QWORD PTR [rsp+184]
	sub r10, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
2112:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 2112b
	mov r8d, 0
2113:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2113b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
2114:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
2115:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 2115b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 2114b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
2116:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2116b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 34
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 2101f
2100:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2117:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2117b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
2101:
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_decrypt_crt_adx:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked_adx}
	mov r11, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+280], r11
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+32]
	cmp r11, 16
	je 20f
	cmp r11, 20
	je 22f
	cmp r11, 28
	je 24f
	cmp r11, 32
	je 26f
	cmp r11, 48
	je 28f
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 130
	jb 210f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 64
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 65
	mov r9, QWORD PTR [rsp+184]
	sub r9, 65
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
212:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 213f
	jmp 214f
213:
	mov r10, rax
214:
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 215b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 212b
	mov rax, QWORD PTR [rsp+112]
	add rax, 65
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 64
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
216:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 217f
	jmp 218f
217:
	mov r10, rax
218:
	mov r8d, 0
219:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 219b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 216b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
220:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 64
	jne 220b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 129
	mov r10, QWORD PTR [rsp+184]
	sub r10, 129
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
221:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 221b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 129
	mov r10, QWORD PTR [rsp+184]
	sub r10, 129
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
222:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 222b
	mov r8d, 0
223:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 223b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
224:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
225:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 225b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 224b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
226:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 226b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 130
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 211f
210:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
227:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 227b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
211:
	jmp 29f
28:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 98
	jb 228f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 48
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 49
	mov r9, QWORD PTR [rsp+184]
	sub r9, 49
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
230:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 231f
	jmp 232f
231:
	mov r10, rax
232:
	mov r8d, 0
233:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 233b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 230b
	mov rax, QWORD PTR [rsp+112]
	add rax, 49
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 49
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 48
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
234:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 235f
	jmp 236f
235:
	mov r10, rax
236:
	mov r8d, 0
237:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 237b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 234b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 49
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
238:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 48
	jne 238b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 97
	mov r10, QWORD PTR [rsp+184]
	sub r10, 97
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
239:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 239b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 97
	mov r10, QWORD PTR [rsp+184]
	sub r10, 97
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
240:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 240b
	mov r8d, 0
241:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 241b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
242:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
243:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 243b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 242b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
244:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 244b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 98
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 229f
228:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
245:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 245b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
229:
29:
	jmp 27f
26:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 246f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
248:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 249f
	jmp 250f
249:
	mov r10, rax
250:
	mov r8d, 0
251:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 251b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 248b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
252:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 253f
	jmp 254f
253:
	mov r10, rax
254:
	mov r8d, 0
255:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 255b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 252b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
256:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 256b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
257:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 257b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
258:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 258b
	mov r8d, 0
259:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 259b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
260:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
261:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 261b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 260b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
262:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 262b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 247f
246:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
263:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 263b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
247:
27:
	jmp 25f
24:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 58
	jb 264f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 28
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 29
	mov r9, QWORD PTR [rsp+184]
	sub r9, 29
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
266:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 267f
	jmp 268f
267:
	mov r10, rax
268:
	mov r8d, 0
269:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 269b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 266b
	mov rax, QWORD PTR [rsp+112]
	add rax, 29
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 29
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 28
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
270:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 271f
	jmp 272f
271:
	mov r10, rax
272:
	mov r8d, 0
273:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 273b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 270b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 29
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
274:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 28
	jne 274b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 57
	mov r10, QWORD PTR [rsp+184]
	sub r10, 57
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
275:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 275b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 57
	mov r10, QWORD PTR [rsp+184]
	sub r10, 57
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
276:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 276b
	mov r8d, 0
277:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 277b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
278:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
279:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 279b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 278b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
280:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 280b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 58
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 265f
264:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
281:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 281b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
265:
25:
	jmp 23f
22:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 42
	jb 282f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 20
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 21
	mov r9, QWORD PTR [rsp+184]
	sub r9, 21
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
284:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 285f
	jmp 286f
285:
	mov r10, rax
286:
	mov r8d, 0
287:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 287b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 284b
	mov rax, QWORD PTR [rsp+112]
	add rax, 21
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 21
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 20
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
288:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 289f
	jmp 290f
289:
	mov r10, rax
290:
	mov r8d, 0
291:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 291b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 288b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 21
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
292:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 20
	jne 292b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 41
	mov r10, QWORD PTR [rsp+184]
	sub r10, 41
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
293:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 293b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 41
	mov r10, QWORD PTR [rsp+184]
	sub r10, 41
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
294:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 294b
	mov r8d, 0
295:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 295b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
296:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
297:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 297b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 296b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
298:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 298b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 42
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 283f
282:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
299:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 299b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
283:
23:
	jmp 21f
20:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 34
	jb 2100f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 16
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 17
	mov r9, QWORD PTR [rsp+184]
	sub r9, 17
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2102:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2103f
	jmp 2104f
2103:
	mov r10, rax
2104:
	mov r8d, 0
2105:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2105b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2102b
	mov rax, QWORD PTR [rsp+112]
	add rax, 17
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 17
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 16
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2106:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2107f
	jmp 2108f
2107:
	mov r10, rax
2108:
	mov r8d, 0
2109:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2109b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2106b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 17
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
2110:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 16
	jne 2110b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov r10, QWORD PTR [rsp+184]
	sub r10, 33
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
2111:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 2111b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 33
	mov r10, QWORD PTR [rsp+184]
	sub r10, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
2112:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 2112b
	mov r8d, 0
2113:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2113b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
2114:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
2115:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 2115b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 2114b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
2116:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2116b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 34
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 2101f
2100:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2117:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2117b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
2101:
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_decrypt:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+232], rdx
	mov QWORD PTR [rsp+176], rcx
	mov QWORD PTR [rsp+184], r8
	mov QWORD PTR [rsp+192], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+112]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+208]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	call {vg_rsa_private_checked}
	mov r11, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+280], r11
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+32]
	cmp r11, 16
	je 20f
	cmp r11, 20
	je 22f
	cmp r11, 28
	je 24f
	cmp r11, 32
	je 26f
	cmp r11, 48
	je 28f
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 130
	jb 210f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 64
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 65
	mov r9, QWORD PTR [rsp+184]
	sub r9, 65
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
212:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 213f
	jmp 214f
213:
	mov r10, rax
214:
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 215b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 212b
	mov rax, QWORD PTR [rsp+112]
	add rax, 65
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 64
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
216:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 217f
	jmp 218f
217:
	mov r10, rax
218:
	mov r8d, 0
219:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 219b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 216b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
220:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 64
	jne 220b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 129
	mov r10, QWORD PTR [rsp+184]
	sub r10, 129
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
221:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 221b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 129
	mov r10, QWORD PTR [rsp+184]
	sub r10, 129
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
222:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 222b
	mov r8d, 0
223:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 223b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
224:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
225:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 225b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 224b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
226:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 226b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 130
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 211f
210:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
227:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 227b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
211:
	jmp 29f
28:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 98
	jb 228f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 48
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 49
	mov r9, QWORD PTR [rsp+184]
	sub r9, 49
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
230:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 231f
	jmp 232f
231:
	mov r10, rax
232:
	mov r8d, 0
233:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 233b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 230b
	mov rax, QWORD PTR [rsp+112]
	add rax, 49
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 49
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 48
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
234:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 235f
	jmp 236f
235:
	mov r10, rax
236:
	mov r8d, 0
237:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 237b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 234b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 49
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
238:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 48
	jne 238b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 97
	mov r10, QWORD PTR [rsp+184]
	sub r10, 97
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
239:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 239b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 97
	mov r10, QWORD PTR [rsp+184]
	sub r10, 97
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
240:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 240b
	mov r8d, 0
241:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 241b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
242:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
243:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 243b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 242b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
244:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 244b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 98
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 229f
228:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
245:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 245b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
229:
29:
	jmp 27f
26:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 246f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
248:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 249f
	jmp 250f
249:
	mov r10, rax
250:
	mov r8d, 0
251:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 251b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 248b
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
252:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 253f
	jmp 254f
253:
	mov r10, rax
254:
	mov r8d, 0
255:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 255b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 252b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
256:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 32
	jne 256b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
257:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 257b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 65
	mov r10, QWORD PTR [rsp+184]
	sub r10, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
258:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 258b
	mov r8d, 0
259:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 259b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
260:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
261:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 261b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 260b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
262:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 262b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 66
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 247f
246:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
263:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 263b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
247:
27:
	jmp 25f
24:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 58
	jb 264f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 28
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 29
	mov r9, QWORD PTR [rsp+184]
	sub r9, 29
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
266:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 267f
	jmp 268f
267:
	mov r10, rax
268:
	mov r8d, 0
269:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 269b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 266b
	mov rax, QWORD PTR [rsp+112]
	add rax, 29
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 29
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 28
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
270:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 271f
	jmp 272f
271:
	mov r10, rax
272:
	mov r8d, 0
273:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 273b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 270b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 29
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
274:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 28
	jne 274b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 57
	mov r10, QWORD PTR [rsp+184]
	sub r10, 57
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
275:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 275b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 57
	mov r10, QWORD PTR [rsp+184]
	sub r10, 57
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
276:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 276b
	mov r8d, 0
277:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 277b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
278:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
279:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 279b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 278b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
280:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 280b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 58
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 265f
264:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
281:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 281b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
265:
25:
	jmp 23f
22:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 42
	jb 282f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 20
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 21
	mov r9, QWORD PTR [rsp+184]
	sub r9, 21
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
284:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 285f
	jmp 286f
285:
	mov r10, rax
286:
	mov r8d, 0
287:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 287b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 284b
	mov rax, QWORD PTR [rsp+112]
	add rax, 21
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 21
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 20
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
288:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 289f
	jmp 290f
289:
	mov r10, rax
290:
	mov r8d, 0
291:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 291b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 288b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 21
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
292:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 20
	jne 292b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 41
	mov r10, QWORD PTR [rsp+184]
	sub r10, 41
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
293:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 293b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 41
	mov r10, QWORD PTR [rsp+184]
	sub r10, 41
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
294:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 294b
	mov r8d, 0
295:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 295b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
296:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
297:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 297b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 296b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
298:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 298b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 42
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 283f
282:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
299:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 299b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
283:
23:
	jmp 21f
20:
	mov eax, eax
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 34
	jb 2100f
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3392
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 16
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 17
	mov r9, QWORD PTR [rsp+184]
	sub r9, 17
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2102:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2103f
	jmp 2104f
2103:
	mov r10, rax
2104:
	mov r8d, 0
2105:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2105b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2102b
	mov rax, QWORD PTR [rsp+112]
	add rax, 17
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 17
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 16
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2106:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2107f
	jmp 2108f
2107:
	mov r10, rax
2108:
	mov r8d, 0
2109:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2109b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2106b
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3392
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 17
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 0
	movzx edx, BYTE PTR [rsi]
	mov r8d, 0
2110:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx r9d, BYTE PTR [rdi+r8*1]
	xor rax, r9
	or rdx, rax
	add r8, 1
	cmp r8, 16
	jne 2110b
	mov QWORD PTR [rsp+248], rdx
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 33
	mov r10, QWORD PTR [rsp+184]
	sub r10, 33
	mov rdx, -1
	mov esi, 0
	mov rcx, QWORD PTR [rsp+248]
	mov r8d, 0
2111:
	movzx eax, BYTE PTR [rdi+r8*1]
	mov r9, rax
	cmp r9, 1
	sbb r9, r9
	mov r11, rax
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rax, r9
	or rax, r11
	xor rax, -1
	and rax, rdx
	or rcx, rax
	mov rax, r8
	and rax, rdx
	and rax, r11
	or rsi, rax
	xor r11, -1
	and rdx, r11
	add r8, 1
	cmp r8, r10
	jne 2111b
	or rcx, rdx
	mov QWORD PTR [rsp+248], rcx
	mov QWORD PTR [rsp+256], rsi
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 33
	mov r10, QWORD PTR [rsp+184]
	sub r10, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov eax, 0
	mov r8d, 0
2112:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 2048
	jne 2112b
	mov r8d, 0
2113:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2113b
	mov rax, QWORD PTR [rsp+256]
	add rax, 1
	mov QWORD PTR [rsp+272], rax
	mov edx, 1
	mov r10d, 10
2114:
	mov rsi, rdx
	add rsi, rcx
	mov r11, QWORD PTR [rsp+272]
	and r11, 1
	mov r9d, 0
	sub r9, r11
	mov r8d, 0
2115:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edi, BYTE PTR [rsi+r8*1]
	xor rdi, rax
	and rdi, r9
	xor rax, rdi
	mov BYTE PTR [rcx+r8*1], al
	add r8, 1
	cmp r8, 1024
	jne 2115b
	mov rax, QWORD PTR [rsp+272]
	shr rax, 1
	mov QWORD PTR [rsp+272], rax
	add rdx, rdx
	sub r10, 1
	jne 2114b
	mov rax, QWORD PTR [rsp+240]
	xor rax, 1
	cmp rax, 1
	sbb rax, rax
	mov r11, QWORD PTR [rsp+248]
	cmp r11, 1
	sbb r11, r11
	and r11, rax
	mov QWORD PTR [rsp+264], r11
	mov rdi, QWORD PTR [rsp+168]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1024
	mov r10, QWORD PTR [rsp+184]
	mov r11, QWORD PTR [rsp+264]
	mov r8d, 0
2116:
	movzx eax, BYTE PTR [rcx+r8*1]
	and rax, r11
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2116b
	mov r11, QWORD PTR [rsp+264]
	mov rax, QWORD PTR [rsp+184]
	sub rax, 34
	sub rax, QWORD PTR [rsp+256]
	and rax, r11
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	and r11, 1
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
	or rax, r11
	jmp 2101f
2100:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2117:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2117b
	mov rdi, QWORD PTR [rsp+232]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsp+240]
	xor rax, 2
	cmp rax, 1
	sbb rax, rax
	and rax, 2
2101:
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_encrypt_precomputed_rsa_ifma:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+208], rax
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+32]
	cmp r11, 16
	je 20f
	cmp r11, 20
	je 22f
	cmp r11, 28
	je 24f
	cmp r11, 32
	je 26f
	cmp r11, 48
	je 28f
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 130
	jb 210f
	sub rax, 130
	cmp rax, QWORD PTR [rsp+240]
	jb 212f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
214:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 214b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 64
	jne 215b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+65], al
	add r8, 1
	cmp r8, 64
	jne 216b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 217f
219:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 219b
	jmp 218f
217:
218:
	mov rax, QWORD PTR [rsp+112]
	add rax, 65
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 64
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
220:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 221f
	jmp 222f
221:
	mov r10, rax
222:
	mov r8d, 0
223:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 223b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 220b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 64
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 65
	mov r9, QWORD PTR [rsp+184]
	sub r9, 65
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
224:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 225f
	jmp 226f
225:
	mov r10, rax
226:
	mov r8d, 0
227:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 227b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 224b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked_ifma}
	jmp 213f
212:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
228:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 228b
213:
	jmp 211f
210:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
229:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 229b
211:
	jmp 29f
28:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 98
	jb 230f
	sub rax, 98
	cmp rax, QWORD PTR [rsp+240]
	jb 232f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
234:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 234b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
235:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 48
	jne 235b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
236:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+49], al
	add r8, 1
	cmp r8, 48
	jne 236b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 237f
239:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 239b
	jmp 238f
237:
238:
	mov rax, QWORD PTR [rsp+112]
	add rax, 49
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 49
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 48
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
240:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 241f
	jmp 242f
241:
	mov r10, rax
242:
	mov r8d, 0
243:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 243b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 240b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 48
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 49
	mov r9, QWORD PTR [rsp+184]
	sub r9, 49
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
244:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 245f
	jmp 246f
245:
	mov r10, rax
246:
	mov r8d, 0
247:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 247b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 244b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked_ifma}
	jmp 233f
232:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
248:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 248b
233:
	jmp 231f
230:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
249:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 249b
231:
29:
	jmp 27f
26:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 250f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 252f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
254:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 254b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
255:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 255b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
256:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 256b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 257f
259:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 259b
	jmp 258f
257:
258:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
260:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 261f
	jmp 262f
261:
	mov r10, rax
262:
	mov r8d, 0
263:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 263b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 260b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
264:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 265f
	jmp 266f
265:
	mov r10, rax
266:
	mov r8d, 0
267:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 267b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 264b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked_ifma}
	jmp 253f
252:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
268:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 268b
253:
	jmp 251f
250:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
269:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 269b
251:
27:
	jmp 25f
24:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 58
	jb 270f
	sub rax, 58
	cmp rax, QWORD PTR [rsp+240]
	jb 272f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
274:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 274b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
275:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 28
	jne 275b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
276:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+29], al
	add r8, 1
	cmp r8, 28
	jne 276b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 277f
279:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 279b
	jmp 278f
277:
278:
	mov rax, QWORD PTR [rsp+112]
	add rax, 29
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 29
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 28
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
280:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 281f
	jmp 282f
281:
	mov r10, rax
282:
	mov r8d, 0
283:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 283b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 280b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 28
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 29
	mov r9, QWORD PTR [rsp+184]
	sub r9, 29
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
284:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 285f
	jmp 286f
285:
	mov r10, rax
286:
	mov r8d, 0
287:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 287b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 284b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked_ifma}
	jmp 273f
272:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
288:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 288b
273:
	jmp 271f
270:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
289:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 289b
271:
25:
	jmp 23f
22:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 42
	jb 290f
	sub rax, 42
	cmp rax, QWORD PTR [rsp+240]
	jb 292f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
294:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 294b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
295:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 20
	jne 295b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
296:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+21], al
	add r8, 1
	cmp r8, 20
	jne 296b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 297f
299:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 299b
	jmp 298f
297:
298:
	mov rax, QWORD PTR [rsp+112]
	add rax, 21
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 21
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 20
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2100:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2101f
	jmp 2102f
2101:
	mov r10, rax
2102:
	mov r8d, 0
2103:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2103b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2100b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 20
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 21
	mov r9, QWORD PTR [rsp+184]
	sub r9, 21
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2104:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2105f
	jmp 2106f
2105:
	mov r10, rax
2106:
	mov r8d, 0
2107:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2107b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2104b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked_ifma}
	jmp 293f
292:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2108:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2108b
293:
	jmp 291f
290:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2109:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2109b
291:
23:
	jmp 21f
20:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 34
	jb 2110f
	sub rax, 34
	cmp rax, QWORD PTR [rsp+240]
	jb 2112f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
2114:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 2114b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
2115:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 16
	jne 2115b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
2116:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+17], al
	add r8, 1
	cmp r8, 16
	jne 2116b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 2117f
2119:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 2119b
	jmp 2118f
2117:
2118:
	mov rax, QWORD PTR [rsp+112]
	add rax, 17
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 17
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 16
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2120:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2121f
	jmp 2122f
2121:
	mov r10, rax
2122:
	mov r8d, 0
2123:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2123b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2120b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 16
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 17
	mov r9, QWORD PTR [rsp+184]
	sub r9, 17
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2124:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2125f
	jmp 2126f
2125:
	mov r10, rax
2126:
	mov r8d, 0
2127:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2127b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2124b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked_ifma}
	jmp 2113f
2112:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2128:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2128b
2113:
	jmp 2111f
2110:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2129:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2129b
2111:
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_encrypt_precomputed_rsa_adx:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+208], rax
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+32]
	cmp r11, 16
	je 20f
	cmp r11, 20
	je 22f
	cmp r11, 28
	je 24f
	cmp r11, 32
	je 26f
	cmp r11, 48
	je 28f
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 130
	jb 210f
	sub rax, 130
	cmp rax, QWORD PTR [rsp+240]
	jb 212f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
214:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 214b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 64
	jne 215b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+65], al
	add r8, 1
	cmp r8, 64
	jne 216b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 217f
219:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 219b
	jmp 218f
217:
218:
	mov rax, QWORD PTR [rsp+112]
	add rax, 65
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 64
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
220:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 221f
	jmp 222f
221:
	mov r10, rax
222:
	mov r8d, 0
223:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 223b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 220b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 64
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 65
	mov r9, QWORD PTR [rsp+184]
	sub r9, 65
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
224:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 225f
	jmp 226f
225:
	mov r10, rax
226:
	mov r8d, 0
227:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 227b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 224b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked_adx}
	jmp 213f
212:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
228:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 228b
213:
	jmp 211f
210:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
229:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 229b
211:
	jmp 29f
28:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 98
	jb 230f
	sub rax, 98
	cmp rax, QWORD PTR [rsp+240]
	jb 232f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
234:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 234b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
235:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 48
	jne 235b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
236:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+49], al
	add r8, 1
	cmp r8, 48
	jne 236b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 237f
239:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 239b
	jmp 238f
237:
238:
	mov rax, QWORD PTR [rsp+112]
	add rax, 49
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 49
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 48
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
240:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 241f
	jmp 242f
241:
	mov r10, rax
242:
	mov r8d, 0
243:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 243b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 240b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 48
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 49
	mov r9, QWORD PTR [rsp+184]
	sub r9, 49
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
244:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 245f
	jmp 246f
245:
	mov r10, rax
246:
	mov r8d, 0
247:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 247b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 244b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked_adx}
	jmp 233f
232:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
248:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 248b
233:
	jmp 231f
230:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
249:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 249b
231:
29:
	jmp 27f
26:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 250f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 252f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
254:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 254b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
255:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 255b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
256:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 256b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 257f
259:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 259b
	jmp 258f
257:
258:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
260:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 261f
	jmp 262f
261:
	mov r10, rax
262:
	mov r8d, 0
263:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 263b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 260b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
264:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 265f
	jmp 266f
265:
	mov r10, rax
266:
	mov r8d, 0
267:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 267b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 264b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked_adx}
	jmp 253f
252:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
268:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 268b
253:
	jmp 251f
250:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
269:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 269b
251:
27:
	jmp 25f
24:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 58
	jb 270f
	sub rax, 58
	cmp rax, QWORD PTR [rsp+240]
	jb 272f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
274:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 274b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
275:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 28
	jne 275b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
276:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+29], al
	add r8, 1
	cmp r8, 28
	jne 276b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 277f
279:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 279b
	jmp 278f
277:
278:
	mov rax, QWORD PTR [rsp+112]
	add rax, 29
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 29
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 28
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
280:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 281f
	jmp 282f
281:
	mov r10, rax
282:
	mov r8d, 0
283:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 283b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 280b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 28
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 29
	mov r9, QWORD PTR [rsp+184]
	sub r9, 29
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
284:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 285f
	jmp 286f
285:
	mov r10, rax
286:
	mov r8d, 0
287:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 287b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 284b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked_adx}
	jmp 273f
272:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
288:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 288b
273:
	jmp 271f
270:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
289:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 289b
271:
25:
	jmp 23f
22:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 42
	jb 290f
	sub rax, 42
	cmp rax, QWORD PTR [rsp+240]
	jb 292f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
294:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 294b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
295:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 20
	jne 295b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
296:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+21], al
	add r8, 1
	cmp r8, 20
	jne 296b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 297f
299:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 299b
	jmp 298f
297:
298:
	mov rax, QWORD PTR [rsp+112]
	add rax, 21
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 21
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 20
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2100:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2101f
	jmp 2102f
2101:
	mov r10, rax
2102:
	mov r8d, 0
2103:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2103b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2100b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 20
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 21
	mov r9, QWORD PTR [rsp+184]
	sub r9, 21
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2104:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2105f
	jmp 2106f
2105:
	mov r10, rax
2106:
	mov r8d, 0
2107:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2107b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2104b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked_adx}
	jmp 293f
292:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2108:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2108b
293:
	jmp 291f
290:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2109:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2109b
291:
23:
	jmp 21f
20:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 34
	jb 2110f
	sub rax, 34
	cmp rax, QWORD PTR [rsp+240]
	jb 2112f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
2114:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 2114b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
2115:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 16
	jne 2115b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
2116:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+17], al
	add r8, 1
	cmp r8, 16
	jne 2116b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 2117f
2119:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 2119b
	jmp 2118f
2117:
2118:
	mov rax, QWORD PTR [rsp+112]
	add rax, 17
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 17
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 16
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2120:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2121f
	jmp 2122f
2121:
	mov r10, rax
2122:
	mov r8d, 0
2123:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2123b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2120b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 16
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 17
	mov r9, QWORD PTR [rsp+184]
	sub r9, 17
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2124:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2125f
	jmp 2126f
2125:
	mov r10, rax
2126:
	mov r8d, 0
2127:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2127b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2124b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked_adx}
	jmp 2113f
2112:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2128:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2128b
2113:
	jmp 2111f
2110:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2129:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2129b
2111:
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6

vg_rsa_oaep_encrypt_precomputed:
	lea rsp, [rsp-296]
	mov QWORD PTR [rsp+168], rdi
	mov QWORD PTR [rsp+176], rdx
	mov QWORD PTR [rsp+184], rcx
	mov QWORD PTR [rsp+192], r8
	mov QWORD PTR [rsp+200], r9
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+208], rax
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+32]
	cmp r11, 16
	je 20f
	cmp r11, 20
	je 22f
	cmp r11, 28
	je 24f
	cmp r11, 32
	je 26f
	cmp r11, 48
	je 28f
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 130
	jb 210f
	sub rax, 130
	cmp rax, QWORD PTR [rsp+240]
	jb 212f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
214:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 214b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
215:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 64
	jne 215b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
216:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+65], al
	add r8, 1
	cmp r8, 64
	jne 216b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 217f
219:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 219b
	jmp 218f
217:
218:
	mov rax, QWORD PTR [rsp+112]
	add rax, 65
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 65
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 64
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
220:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 221f
	jmp 222f
221:
	mov r10, rax
222:
	mov r8d, 0
223:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 223b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 220b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 64
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 65
	mov r9, QWORD PTR [rsp+184]
	sub r9, 65
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
224:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 225f
	jmp 226f
225:
	mov r10, rax
226:
	mov r8d, 0
227:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 227b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 224b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked}
	jmp 213f
212:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
228:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 228b
213:
	jmp 211f
210:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
229:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 229b
211:
	jmp 29f
28:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 98
	jb 230f
	sub rax, 98
	cmp rax, QWORD PTR [rsp+240]
	jb 232f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
234:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 234b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
235:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 48
	jne 235b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
236:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+49], al
	add r8, 1
	cmp r8, 48
	jne 236b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 237f
239:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 239b
	jmp 238f
237:
238:
	mov rax, QWORD PTR [rsp+112]
	add rax, 49
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 49
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 48
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
240:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 241f
	jmp 242f
241:
	mov r10, rax
242:
	mov r8d, 0
243:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 243b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 240b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 48
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 49
	mov r9, QWORD PTR [rsp+184]
	sub r9, 49
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
244:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 245f
	jmp 246f
245:
	mov r10, rax
246:
	mov r8d, 0
247:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 247b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 244b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked}
	jmp 233f
232:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
248:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 248b
233:
	jmp 231f
230:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
249:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 249b
231:
29:
	jmp 27f
26:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 66
	jb 250f
	sub rax, 66
	cmp rax, QWORD PTR [rsp+240]
	jb 252f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
254:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 254b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
255:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 32
	jne 255b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
256:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+33], al
	add r8, 1
	cmp r8, 32
	jne 256b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 257f
259:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 259b
	jmp 258f
257:
258:
	mov rax, QWORD PTR [rsp+112]
	add rax, 33
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 33
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 32
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
260:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 261f
	jmp 262f
261:
	mov r10, rax
262:
	mov r8d, 0
263:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 263b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 260b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 32
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 33
	mov r9, QWORD PTR [rsp+184]
	sub r9, 33
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
264:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 265f
	jmp 266f
265:
	mov r10, rax
266:
	mov r8d, 0
267:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 267b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 264b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked}
	jmp 253f
252:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
268:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 268b
253:
	jmp 251f
250:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
269:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 269b
251:
27:
	jmp 25f
24:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 58
	jb 270f
	sub rax, 58
	cmp rax, QWORD PTR [rsp+240]
	jb 272f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
274:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 274b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
275:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 28
	jne 275b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
276:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+29], al
	add r8, 1
	cmp r8, 28
	jne 276b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 277f
279:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 279b
	jmp 278f
277:
278:
	mov rax, QWORD PTR [rsp+112]
	add rax, 29
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 29
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 28
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
280:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 281f
	jmp 282f
281:
	mov r10, rax
282:
	mov r8d, 0
283:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 283b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 280b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 28
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 29
	mov r9, QWORD PTR [rsp+184]
	sub r9, 29
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
284:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 285f
	jmp 286f
285:
	mov r10, rax
286:
	mov r8d, 0
287:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 287b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 284b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked}
	jmp 273f
272:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
288:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 288b
273:
	jmp 271f
270:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
289:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 289b
271:
25:
	jmp 23f
22:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 42
	jb 290f
	sub rax, 42
	cmp rax, QWORD PTR [rsp+240]
	jb 292f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
294:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 294b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
295:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 20
	jne 295b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
296:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+21], al
	add r8, 1
	cmp r8, 20
	jne 296b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 297f
299:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 299b
	jmp 298f
297:
298:
	mov rax, QWORD PTR [rsp+112]
	add rax, 21
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 21
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 20
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2100:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2101f
	jmp 2102f
2101:
	mov r10, rax
2102:
	mov r8d, 0
2103:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2103b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2100b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 20
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 21
	mov r9, QWORD PTR [rsp+184]
	sub r9, 21
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2104:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2105f
	jmp 2106f
2105:
	mov r10, rax
2106:
	mov r8d, 0
2107:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2107b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2104b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked}
	jmp 293f
292:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2108:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2108b
293:
	jmp 291f
290:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2109:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2109b
291:
23:
	jmp 21f
20:
	mov rax, QWORD PTR [rsp+184]
	cmp rax, 34
	jb 2110f
	sub rax, 34
	cmp rax, QWORD PTR [rsp+240]
	jb 2112f
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov eax, 0
	mov r8d, 0
2114:
	mov QWORD PTR [rcx+r8*1], rax
	add r8, 8
	cmp r8, 1024
	jne 2114b
	mov rsi, QWORD PTR [rsp+248]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
2115:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+1], al
	add r8, 1
	cmp r8, 16
	jne 2115b
	mov r11, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+280], r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rsi, QWORD PTR [rsp+112]
	add rsi, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 0
	mov r8d, 0
2116:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rcx+r8*1+17], al
	add r8, 1
	cmp r8, 16
	jne 2116b
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 0
	mov rax, QWORD PTR [rsp+184]
	add rdi, rax
	mov rax, QWORD PTR [rsp+240]
	sub rdi, rax
	sub rdi, 1
	mov eax, 1
	mov BYTE PTR [rdi], al
	mov rsi, QWORD PTR [rsp+232]
	mov r10, QWORD PTR [rsp+240]
	mov r8d, 0
	test r10, r10
	je 2117f
2119:
	movzx eax, BYTE PTR [rsi+r8*1]
	mov BYTE PTR [rdi+r8*1+1], al
	add r8, 1
	cmp r8, r10
	jne 2119b
	jmp 2118f
2117:
2118:
	mov rax, QWORD PTR [rsp+112]
	add rax, 17
	mov rdx, QWORD PTR [rsp+184]
	sub rdx, 17
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 1
	mov r9d, 16
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2120:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2121f
	jmp 2122f
2121:
	mov r10, rax
2122:
	mov r8d, 0
2123:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2123b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2120b
	mov rax, QWORD PTR [rsp+112]
	add rax, 1
	mov edx, 16
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 17
	mov r9, QWORD PTR [rsp+184]
	sub r9, 17
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+120], rcx
	mov QWORD PTR [rsp+128], r9
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+280], rax
	mov rax, QWORD PTR [rsp+280]
	mov rax, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+288], rax
	mov eax, 0
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
2124:
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov esi, 0
	mov rdx, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+128]
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3456
	mov rax, QWORD PTR [rsp+152]
	mov BYTE PTR [rdx+3], al
	shr rax, 8
	mov BYTE PTR [rdx+2], al
	shr rax, 8
	mov BYTE PTR [rdx+1], al
	shr rax, 8
	mov BYTE PTR [rdx], al
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	mov ecx, 4
	mov r8, QWORD PTR [rsp+112]
	add r8, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+8]
	call r11
	mov rdi, QWORD PTR [rsp+112]
	add rdi, 3072
	mov rsi, QWORD PTR [rsp+128]
	add rsi, 4
	mov rdx, QWORD PTR [rsp+112]
	add rdx, 3328
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 4096
	mov r11, QWORD PTR [rsp+280]
	mov r11, QWORD PTR [r11+16]
	call r11
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 3328
	mov rdx, QWORD PTR [rsp+160]
	mov rdi, QWORD PTR [rsp+136]
	add rdi, rdx
	mov rax, QWORD PTR [rsp+144]
	sub rax, rdx
	mov r10, QWORD PTR [rsp+288]
	cmp rax, r10
	jb 2125f
	jmp 2126f
2125:
	mov r10, rax
2126:
	mov r8d, 0
2127:
	movzx eax, BYTE PTR [rcx+r8*1]
	movzx edx, BYTE PTR [rdi+r8*1]
	xor rdx, rax
	mov BYTE PTR [rdi+r8*1], dl
	add r8, 1
	cmp r8, r10
	jne 2127b
	mov rax, QWORD PTR [rsp+152]
	add rax, 1
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+160]
	add rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+160], rax
	cmp rax, QWORD PTR [rsp+144]
	jb 2124b
	mov rax, QWORD PTR [rsp+112]
	add rax, 0
	mov rdx, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+112]
	add rcx, 8192
	mov r9, QWORD PTR [rsp+208]
	sub r9, 1024
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rdx
	mov QWORD PTR [rsp+16], rcx
	mov QWORD PTR [rsp+24], r9
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+184]
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+184]
	mov r8, QWORD PTR [rsp+192]
	mov r9, QWORD PTR [rsp+200]
	mov rdx, QWORD PTR [rsp+368]
	mov rcx, QWORD PTR [rsp+376]
	call {vg_rsa_public_precomputed_checked}
	jmp 2113f
2112:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2128:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2128b
2113:
	jmp 2111f
2110:
	mov rdi, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+184]
	mov eax, 0
	mov r8d, 0
2129:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 2129b
2111:
21:
	lea rsp, [rsp+296]
	ret
	.p2align 6
