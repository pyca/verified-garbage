// The functions of `src/internal/vg_rsa_crt_ifma_3072.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_crt_ifma_3072:
	mov rdx, QWORD PTR [rdi+240]
	mov rax, QWORD PTR [rdx+120]
	mov rdx, QWORD PTR [rdx+48]
	add rdx, 2
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	add rax, rdx
	mov rdx, QWORD PTR [rdi+232]
	mov QWORD PTR [rdx+232], rax
	mov rdx, QWORD PTR [rdi+240]
	mov QWORD PTR [rdx+232], rax
	mov rdi, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
20:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 20b
	mov ecx, 48
	mov QWORD PTR [rdi+240], rcx
21:
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
22:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 22b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
23:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 23b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
24:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 24b
	mov rcx, QWORD PTR [rdi+240]
	sub rcx, 1
	mov QWORD PTR [rdi+240], rcx
	jne 21b
	mov r8d, 5
25:
	cmp r8, 5
	je 26f
	cmp r8, 4
	je 28f
	cmp r8, 3
	je 210f
	cmp r8, 2
	je 212f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 10080
	movabs r12, 4503599627370495
	jmp 213f
212:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 288
	movabs r12, 4503599627370495
213:
	jmp 211f
210:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 544
	movabs r12, 4503599627370495
211:
	jmp 29f
28:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 9792
	movabs r12, 4503599627370495
29:
	jmp 27f
26:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 0
	movabs r12, 4503599627370495
27:
	mov rax, QWORD PTR [rsi]
	and rax, r12
	mov QWORD PTR [r11], rax
	mov rax, QWORD PTR [rsi]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+8]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	mov rax, QWORD PTR [rsi+8]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+16]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsi+16]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+24]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	mov rax, QWORD PTR [rsi+24]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+32]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+160], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+40]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	mov rax, QWORD PTR [rsi+40]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+48]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	mov rax, QWORD PTR [rsi+48]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+56]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+56]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+64]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov eax, 0
	mov QWORD PTR [r11+216], rax
	mov eax, 0
	mov QWORD PTR [r11+248], rax
	sub r8, 1
	jne 25b
	mov r11, QWORD PTR [rdi+232]
	add r11, 0
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [r11+256], rax
	mov QWORD PTR [r11+264], rax
	mov QWORD PTR [r11+272], rax
	mov QWORD PTR [r11+280], rax
	mov eax, 0
	mov QWORD PTR [r11+9248], rax
	mov QWORD PTR [r11+9256], rax
	mov QWORD PTR [r11+9264], rax
	mov QWORD PTR [r11+9272], rax
	mov QWORD PTR [r11+9280], rax
	mov QWORD PTR [r11+9288], rax
	mov QWORD PTR [r11+9296], rax
	mov QWORD PTR [r11+9304], rax
	mov QWORD PTR [r11+9312], rax
	mov QWORD PTR [r11+9320], rax
	mov QWORD PTR [r11+9328], rax
	mov QWORD PTR [r11+9336], rax
	mov QWORD PTR [r11+9344], rax
	mov QWORD PTR [r11+9352], rax
	mov QWORD PTR [r11+9360], rax
	mov QWORD PTR [r11+9368], rax
	mov QWORD PTR [r11+9376], rax
	mov QWORD PTR [r11+9384], rax
	mov QWORD PTR [r11+9392], rax
	mov QWORD PTR [r11+9400], rax
	mov QWORD PTR [r11+9408], rax
	mov QWORD PTR [r11+9416], rax
	mov QWORD PTR [r11+9424], rax
	mov QWORD PTR [r11+9432], rax
	mov QWORD PTR [r11+9440], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+200]
	mov rcx, QWORD PTR [rax+160]
	add r11, 9443
	sub r11, rcx
214:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 214b
	mov r8, QWORD PTR [rdi+232]
	add r8, 9248
	mov r9, QWORD PTR [rdi+232]
	add r9, 9472
	mov ecx, 39
215:
	mov eax, 0
	shl rax, 8
	movzx edx, BYTE PTR [r8]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+1]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+2]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+3]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+4]
	or rax, rdx
	mov rdx, rax
	shr rdx, 35
	and rdx, 31
	mov BYTE PTR [r9], dl
	mov rdx, rax
	shr rdx, 30
	and rdx, 31
	mov BYTE PTR [r9+1], dl
	mov rdx, rax
	shr rdx, 25
	and rdx, 31
	mov BYTE PTR [r9+2], dl
	mov rdx, rax
	shr rdx, 20
	and rdx, 31
	mov BYTE PTR [r9+3], dl
	mov rdx, rax
	shr rdx, 15
	and rdx, 31
	mov BYTE PTR [r9+4], dl
	mov rdx, rax
	shr rdx, 10
	and rdx, 31
	mov BYTE PTR [r9+5], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 31
	mov BYTE PTR [r9+6], dl
	mov rdx, rax
	and rdx, 31
	mov BYTE PTR [r9+7], dl
	add r8, 5
	add r9, 8
	sub rcx, 1
	jne 215b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+240]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+112]
	mov rbx, QWORD PTR [rdi+104]
	mov r14, 0
216:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 216b
	mov ecx, 48
	mov QWORD PTR [rdi+240], rcx
217:
	mov rbx, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
218:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	adc rax, rax
	mov QWORD PTR [r8+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 218b
	mov eax, 0
	add rbp, rbp
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov ebp, 0
	mov r14, 0
219:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 219b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
220:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 220b
	mov rcx, QWORD PTR [rdi+240]
	sub rcx, 1
	mov QWORD PTR [rdi+240], rcx
	jne 217b
	mov r8d, 5
221:
	cmp r8, 5
	je 222f
	cmp r8, 4
	je 224f
	cmp r8, 3
	je 226f
	cmp r8, 2
	je 228f
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 20416
	movabs r12, 4503599627370495
	jmp 229f
228:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 10624
	movabs r12, 4503599627370495
229:
	jmp 227f
226:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 10880
	movabs r12, 4503599627370495
227:
	jmp 225f
224:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 20128
	movabs r12, 4503599627370495
225:
	jmp 223f
222:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 10336
	movabs r12, 4503599627370495
223:
	mov rax, QWORD PTR [rsi]
	and rax, r12
	mov QWORD PTR [r11], rax
	mov rax, QWORD PTR [rsi]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+8]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	mov rax, QWORD PTR [rsi+8]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+16]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsi+16]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+24]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	mov rax, QWORD PTR [rsi+24]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+32]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+160], rax
	mov rax, QWORD PTR [rsi+32]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+40]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	mov rax, QWORD PTR [rsi+40]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+48]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	mov rax, QWORD PTR [rsi+48]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+56]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+56]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+64]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov eax, 0
	mov QWORD PTR [r11+216], rax
	mov eax, 0
	mov QWORD PTR [r11+248], rax
	sub r8, 1
	jne 221b
	mov r11, QWORD PTR [rdi+232]
	add r11, 10336
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [r11+256], rax
	mov QWORD PTR [r11+264], rax
	mov QWORD PTR [r11+272], rax
	mov QWORD PTR [r11+280], rax
	mov eax, 0
	mov QWORD PTR [r11+9248], rax
	mov QWORD PTR [r11+9256], rax
	mov QWORD PTR [r11+9264], rax
	mov QWORD PTR [r11+9272], rax
	mov QWORD PTR [r11+9280], rax
	mov QWORD PTR [r11+9288], rax
	mov QWORD PTR [r11+9296], rax
	mov QWORD PTR [r11+9304], rax
	mov QWORD PTR [r11+9312], rax
	mov QWORD PTR [r11+9320], rax
	mov QWORD PTR [r11+9328], rax
	mov QWORD PTR [r11+9336], rax
	mov QWORD PTR [r11+9344], rax
	mov QWORD PTR [r11+9352], rax
	mov QWORD PTR [r11+9360], rax
	mov QWORD PTR [r11+9368], rax
	mov QWORD PTR [r11+9376], rax
	mov QWORD PTR [r11+9384], rax
	mov QWORD PTR [r11+9392], rax
	mov QWORD PTR [r11+9400], rax
	mov QWORD PTR [r11+9408], rax
	mov QWORD PTR [r11+9416], rax
	mov QWORD PTR [r11+9424], rax
	mov QWORD PTR [r11+9432], rax
	mov QWORD PTR [r11+9440], rax
	mov QWORD PTR [r11+10080], rax
	mov QWORD PTR [r11+10112], rax
	mov QWORD PTR [r11+10144], rax
	mov QWORD PTR [r11+10176], rax
	mov QWORD PTR [r11+10208], rax
	mov QWORD PTR [r11+10240], rax
	mov QWORD PTR [r11+10272], rax
	mov QWORD PTR [r11+10304], rax
	mov QWORD PTR [r11+10088], rax
	mov QWORD PTR [r11+10120], rax
	mov QWORD PTR [r11+10152], rax
	mov QWORD PTR [r11+10184], rax
	mov QWORD PTR [r11+10216], rax
	mov QWORD PTR [r11+10248], rax
	mov QWORD PTR [r11+10280], rax
	mov QWORD PTR [r11+10312], rax
	mov QWORD PTR [r11+10096], rax
	mov QWORD PTR [r11+10128], rax
	mov QWORD PTR [r11+10160], rax
	mov QWORD PTR [r11+10192], rax
	mov QWORD PTR [r11+10224], rax
	mov QWORD PTR [r11+10256], rax
	mov QWORD PTR [r11+10288], rax
	mov QWORD PTR [r11+10320], rax
	mov QWORD PTR [r11+10104], rax
	mov QWORD PTR [r11+10136], rax
	mov QWORD PTR [r11+10168], rax
	mov QWORD PTR [r11+10200], rax
	mov QWORD PTR [r11+10232], rax
	mov QWORD PTR [r11+10264], rax
	mov QWORD PTR [r11+10296], rax
	mov QWORD PTR [r11+10328], rax
	mov eax, 1
	mov QWORD PTR [r11+10080], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+216]
	mov rcx, QWORD PTR [rax+192]
	add r11, 9443
	sub r11, rcx
230:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 230b
	mov r8, QWORD PTR [rdi+232]
	add r8, 19584
	mov r9, QWORD PTR [rdi+232]
	add r9, 19808
	mov ecx, 39
231:
	mov eax, 0
	shl rax, 8
	movzx edx, BYTE PTR [r8]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+1]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+2]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+3]
	or rax, rdx
	shl rax, 8
	movzx edx, BYTE PTR [r8+4]
	or rax, rdx
	mov rdx, rax
	shr rdx, 35
	and rdx, 31
	mov BYTE PTR [r9], dl
	mov rdx, rax
	shr rdx, 30
	and rdx, 31
	mov BYTE PTR [r9+1], dl
	mov rdx, rax
	shr rdx, 25
	and rdx, 31
	mov BYTE PTR [r9+2], dl
	mov rdx, rax
	shr rdx, 20
	and rdx, 31
	mov BYTE PTR [r9+3], dl
	mov rdx, rax
	shr rdx, 15
	and rdx, 31
	mov BYTE PTR [r9+4], dl
	mov rdx, rax
	shr rdx, 10
	and rdx, 31
	mov BYTE PTR [r9+5], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 31
	mov BYTE PTR [r9+6], dl
	mov rdx, rax
	and rdx, 31
	mov BYTE PTR [r9+7], dl
	add r8, 5
	add r9, 8
	sub rcx, 1
	jne 231b
	mov rbx, QWORD PTR [rdi+232]
	mov r13d, 1056
232:
	cmp r13, 1568
	jb 233f
	mov r8, rbx
	add r8, r13
	sub r8, 256
	mov r9, rbx
	add r9, 544
	mov r11, rbx
	add r11, r13
	jmp 234f
233:
	mov r8, rbx
	add r8, r13
	sub r8, 768
	mov r9, rbx
	add r9, 9792
	mov r11, r8
234:
	mov r10, rbx
	mov ecx, 3
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpxorq ymm8, ymm8, ymm8
	vpxorq ymm9, ymm9, ymm9
	vpxorq ymm10, ymm10, ymm10
	vpxorq ymm11, ymm11, ymm11
	vpxorq ymm12, ymm12, ymm12
	vpxorq ymm13, ymm13, ymm13
	vpxorq ymm14, ymm14, ymm14
	vpxorq ymm15, ymm15, ymm15
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpxorq ymm19, ymm19, ymm19
	vpxorq ymm20, ymm20, ymm20
235:
	mov rax, QWORD PTR [r9]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10336]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm0, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm8, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm0, 52
	vmovq xmm21, xmm21
	vpaddq ymm1, ymm1, ymm21
	valignq ymm0, ymm20, ymm0, 1
	vpsrlq ymm21, ymm8, 52
	vmovq xmm21, xmm21
	vpaddq ymm9, ymm9, ymm21
	valignq ymm8, ymm20, ymm8, 1
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10368]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm1, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm9, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm1, 52
	vmovq xmm21, xmm21
	vpaddq ymm2, ymm2, ymm21
	valignq ymm1, ymm20, ymm1, 1
	vpsrlq ymm21, ymm9, 52
	vmovq xmm21, xmm21
	vpaddq ymm10, ymm10, ymm21
	valignq ymm9, ymm20, ymm9, 1
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10400]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm2, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm10, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm2, 52
	vmovq xmm21, xmm21
	vpaddq ymm3, ymm3, ymm21
	valignq ymm2, ymm20, ymm2, 1
	vpsrlq ymm21, ymm10, 52
	vmovq xmm21, xmm21
	vpaddq ymm11, ymm11, ymm21
	valignq ymm10, ymm20, ymm10, 1
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10432]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm3, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm11, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm3, 52
	vmovq xmm21, xmm21
	vpaddq ymm4, ymm4, ymm21
	valignq ymm3, ymm20, ymm3, 1
	vpsrlq ymm21, ymm11, 52
	vmovq xmm21, xmm21
	vpaddq ymm12, ymm12, ymm21
	valignq ymm11, ymm20, ymm11, 1
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10464]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm4, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm12, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm4, 52
	vmovq xmm21, xmm21
	vpaddq ymm5, ymm5, ymm21
	valignq ymm4, ymm20, ymm4, 1
	vpsrlq ymm21, ymm12, 52
	vmovq xmm21, xmm21
	vpaddq ymm13, ymm13, ymm21
	valignq ymm12, ymm20, ymm12, 1
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10496]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm5, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm13, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm5, 52
	vmovq xmm21, xmm21
	vpaddq ymm6, ymm6, ymm21
	valignq ymm5, ymm20, ymm5, 1
	vpsrlq ymm21, ymm13, 52
	vmovq xmm21, xmm21
	vpaddq ymm14, ymm14, ymm21
	valignq ymm13, ymm20, ymm13, 1
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10528]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm6, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm14, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm6, 52
	vmovq xmm21, xmm21
	vpaddq ymm7, ymm7, ymm21
	valignq ymm6, ymm20, ymm6, 1
	vpsrlq ymm21, ymm14, 52
	vmovq xmm21, xmm21
	vpaddq ymm15, ymm15, ymm21
	valignq ymm14, ymm20, ymm14, 1
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10560]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm7, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm15, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm7, 52
	vmovq xmm21, xmm21
	vpaddq ymm0, ymm0, ymm21
	valignq ymm7, ymm20, ymm7, 1
	vpsrlq ymm21, ymm15, 52
	vmovq xmm21, xmm21
	vpaddq ymm8, ymm8, ymm21
	valignq ymm15, ymm20, ymm15, 1
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10560]
	add r9, 8
	sub rcx, 1
	jne 235b
	mov rax, QWORD PTR [r9]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10336]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm0, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm8, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm0, 52
	vmovq xmm21, xmm21
	vpaddq ymm1, ymm1, ymm21
	valignq ymm0, ymm20, ymm0, 1
	vpsrlq ymm21, ymm8, 52
	vmovq xmm21, xmm21
	vpaddq ymm9, ymm9, ymm21
	valignq ymm8, ymm20, ymm8, 1
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10368]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm1, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm9, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm1, 52
	vmovq xmm21, xmm21
	vpaddq ymm2, ymm2, ymm21
	valignq ymm1, ymm20, ymm1, 1
	vpsrlq ymm21, ymm9, 52
	vmovq xmm21, xmm21
	vpaddq ymm10, ymm10, ymm21
	valignq ymm9, ymm20, ymm9, 1
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10400]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm2, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm10, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm2, 52
	vmovq xmm21, xmm21
	vpaddq ymm3, ymm3, ymm21
	valignq ymm2, ymm20, ymm2, 1
	vpsrlq ymm21, ymm10, 52
	vmovq xmm21, xmm21
	vpaddq ymm11, ymm11, ymm21
	valignq ymm10, ymm20, ymm10, 1
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10432]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm3, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm11, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm3, 52
	vmovq xmm21, xmm21
	vpaddq ymm4, ymm4, ymm21
	valignq ymm3, ymm20, ymm3, 1
	vpsrlq ymm21, ymm11, 52
	vmovq xmm21, xmm21
	vpaddq ymm12, ymm12, ymm21
	valignq ymm11, ymm20, ymm11, 1
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10464]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm4, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm12, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm4, 52
	vmovq xmm21, xmm21
	vpaddq ymm5, ymm5, ymm21
	valignq ymm4, ymm20, ymm4, 1
	vpsrlq ymm21, ymm12, 52
	vmovq xmm21, xmm21
	vpaddq ymm13, ymm13, ymm21
	valignq ymm12, ymm20, ymm12, 1
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10496]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm5, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm13, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm5, 52
	vmovq xmm21, xmm21
	vpaddq ymm6, ymm6, ymm21
	valignq ymm5, ymm20, ymm5, 1
	vpsrlq ymm21, ymm13, 52
	vmovq xmm21, xmm21
	vpaddq ymm14, ymm14, ymm21
	valignq ymm13, ymm20, ymm13, 1
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10560]
	movabs r12, 4503599627370495
	vmovq xmm24, r12
	vpbroadcastq ymm24, xmm24
	mov eax, 1
	vmovq xmm25, rax
	vpbroadcastq ymm25, xmm25
	vpxorq ymm26, ymm26, ymm26
	mov esi, 16843009
	vpsrlq ymm16, ymm6, 52
	vpandq ymm6, ymm6, ymm24
	vpsrlq ymm17, ymm7, 52
	vpandq ymm7, ymm7, ymm24
	vpsrlq ymm18, ymm0, 52
	vpandq ymm0, ymm0, ymm24
	vpsrlq ymm19, ymm1, 52
	vpandq ymm1, ymm1, ymm24
	vpsrlq ymm20, ymm2, 52
	vpandq ymm2, ymm2, ymm24
	vpsrlq ymm21, ymm3, 52
	vpandq ymm3, ymm3, ymm24
	vpsrlq ymm22, ymm4, 52
	vpandq ymm4, ymm4, ymm24
	vpsrlq ymm23, ymm5, 52
	vpandq ymm5, ymm5, ymm24
	valignq ymm27, ymm23, ymm26, 3
	xor eax, eax
	xor ecx, ecx
	vpaddq ymm6, ymm6, ymm27
	vpcmpuq k1, ymm6, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	or eax, edx
	vpcmpuq k1, ymm6, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	or ecx, edx
	vpaddq ymm7, ymm7, ymm16
	vpcmpuq k1, ymm7, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 1
	or eax, edx
	vpcmpuq k1, ymm7, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 1
	or ecx, edx
	vpaddq ymm0, ymm0, ymm17
	vpcmpuq k1, ymm0, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 2
	or eax, edx
	vpcmpuq k1, ymm0, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 2
	or ecx, edx
	vpaddq ymm1, ymm1, ymm18
	vpcmpuq k1, ymm1, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 3
	or eax, edx
	vpcmpuq k1, ymm1, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 3
	or ecx, edx
	vpaddq ymm2, ymm2, ymm19
	vpcmpuq k1, ymm2, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 4
	or eax, edx
	vpcmpuq k1, ymm2, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 4
	or ecx, edx
	vpaddq ymm3, ymm3, ymm20
	vpcmpuq k1, ymm3, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 5
	or eax, edx
	vpcmpuq k1, ymm3, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 5
	or ecx, edx
	vpaddq ymm4, ymm4, ymm21
	vpcmpuq k1, ymm4, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 6
	or eax, edx
	vpcmpuq k1, ymm4, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 6
	or ecx, edx
	vpaddq ymm5, ymm5, ymm22
	vpcmpuq k1, ymm5, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 7
	or eax, edx
	vpcmpuq k1, ymm5, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 7
	or ecx, edx
	shl rax, 1
	add rax, rcx
	xor rax, rcx
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm6 {k1}, ymm6, ymm25
	kxorw k1, k1, k1
	vpandq ymm6, ymm6, ymm24
	vmovdqu64 YMMWORD PTR [r11], ymm6
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm7 {k1}, ymm7, ymm25
	kxorw k1, k1, k1
	vpandq ymm7, ymm7, ymm24
	vmovdqu64 YMMWORD PTR [r11+32], ymm7
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm0 {k1}, ymm0, ymm25
	kxorw k1, k1, k1
	vpandq ymm0, ymm0, ymm24
	vmovdqu64 YMMWORD PTR [r11+64], ymm0
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm1 {k1}, ymm1, ymm25
	kxorw k1, k1, k1
	vpandq ymm1, ymm1, ymm24
	vmovdqu64 YMMWORD PTR [r11+96], ymm1
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm2 {k1}, ymm2, ymm25
	kxorw k1, k1, k1
	vpandq ymm2, ymm2, ymm24
	vmovdqu64 YMMWORD PTR [r11+128], ymm2
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm3 {k1}, ymm3, ymm25
	kxorw k1, k1, k1
	vpandq ymm3, ymm3, ymm24
	vmovdqu64 YMMWORD PTR [r11+160], ymm3
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm4 {k1}, ymm4, ymm25
	kxorw k1, k1, k1
	vpandq ymm4, ymm4, ymm24
	vmovdqu64 YMMWORD PTR [r11+192], ymm4
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm5 {k1}, ymm5, ymm25
	kxorw k1, k1, k1
	vpandq ymm5, ymm5, ymm24
	vmovdqu64 YMMWORD PTR [r11+224], ymm5
	shr rax, 25
	vpermq ymm6, ymm23, 255
	movq rdx, xmm6
	add rdx, rax
	mov r10, rdx
	vpsrlq ymm16, ymm14, 52
	vpandq ymm14, ymm14, ymm24
	vpsrlq ymm17, ymm15, 52
	vpandq ymm15, ymm15, ymm24
	vpsrlq ymm18, ymm8, 52
	vpandq ymm8, ymm8, ymm24
	vpsrlq ymm19, ymm9, 52
	vpandq ymm9, ymm9, ymm24
	vpsrlq ymm20, ymm10, 52
	vpandq ymm10, ymm10, ymm24
	vpsrlq ymm21, ymm11, 52
	vpandq ymm11, ymm11, ymm24
	vpsrlq ymm22, ymm12, 52
	vpandq ymm12, ymm12, ymm24
	vpsrlq ymm23, ymm13, 52
	vpandq ymm13, ymm13, ymm24
	valignq ymm27, ymm23, ymm26, 3
	xor eax, eax
	xor ecx, ecx
	vpaddq ymm14, ymm14, ymm27
	vpcmpuq k1, ymm14, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	or eax, edx
	vpcmpuq k1, ymm14, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	or ecx, edx
	vpaddq ymm15, ymm15, ymm16
	vpcmpuq k1, ymm15, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 1
	or eax, edx
	vpcmpuq k1, ymm15, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 1
	or ecx, edx
	vpaddq ymm8, ymm8, ymm17
	vpcmpuq k1, ymm8, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 2
	or eax, edx
	vpcmpuq k1, ymm8, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 2
	or ecx, edx
	vpaddq ymm9, ymm9, ymm18
	vpcmpuq k1, ymm9, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 3
	or eax, edx
	vpcmpuq k1, ymm9, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 3
	or ecx, edx
	vpaddq ymm10, ymm10, ymm19
	vpcmpuq k1, ymm10, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 4
	or eax, edx
	vpcmpuq k1, ymm10, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 4
	or ecx, edx
	vpaddq ymm11, ymm11, ymm20
	vpcmpuq k1, ymm11, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 5
	or eax, edx
	vpcmpuq k1, ymm11, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 5
	or ecx, edx
	vpaddq ymm12, ymm12, ymm21
	vpcmpuq k1, ymm12, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 6
	or eax, edx
	vpcmpuq k1, ymm12, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 6
	or ecx, edx
	vpaddq ymm13, ymm13, ymm22
	vpcmpuq k1, ymm13, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 7
	or eax, edx
	vpcmpuq k1, ymm13, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 7
	or ecx, edx
	shl rax, 1
	add rax, rcx
	xor rax, rcx
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm14 {k1}, ymm14, ymm25
	kxorw k1, k1, k1
	vpandq ymm14, ymm14, ymm24
	vmovdqu64 YMMWORD PTR [r11+10336], ymm14
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm15 {k1}, ymm15, ymm25
	kxorw k1, k1, k1
	vpandq ymm15, ymm15, ymm24
	vmovdqu64 YMMWORD PTR [r11+10368], ymm15
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm8 {k1}, ymm8, ymm25
	kxorw k1, k1, k1
	vpandq ymm8, ymm8, ymm24
	vmovdqu64 YMMWORD PTR [r11+10400], ymm8
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm9 {k1}, ymm9, ymm25
	kxorw k1, k1, k1
	vpandq ymm9, ymm9, ymm24
	vmovdqu64 YMMWORD PTR [r11+10432], ymm9
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm10 {k1}, ymm10, ymm25
	kxorw k1, k1, k1
	vpandq ymm10, ymm10, ymm24
	vmovdqu64 YMMWORD PTR [r11+10464], ymm10
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm11 {k1}, ymm11, ymm25
	kxorw k1, k1, k1
	vpandq ymm11, ymm11, ymm24
	vmovdqu64 YMMWORD PTR [r11+10496], ymm11
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm12 {k1}, ymm12, ymm25
	kxorw k1, k1, k1
	vpandq ymm12, ymm12, ymm24
	vmovdqu64 YMMWORD PTR [r11+10528], ymm12
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm13 {k1}, ymm13, ymm25
	kxorw k1, k1, k1
	vpandq ymm13, ymm13, ymm24
	vmovdqu64 YMMWORD PTR [r11+10560], ymm13
	shr rax, 25
	vpermq ymm14, ymm23, 255
	movq rsi, xmm14
	add rsi, rax
	mov rdx, r10
	cmp r13, 1312
	je 236f
	jmp 237f
236:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+288]
	vmovdqu64 YMMWORD PTR [rbx+1056], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+320]
	vmovdqu64 YMMWORD PTR [rbx+1088], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+352]
	vmovdqu64 YMMWORD PTR [rbx+1120], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+384]
	vmovdqu64 YMMWORD PTR [rbx+1152], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+416]
	vmovdqu64 YMMWORD PTR [rbx+1184], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+448]
	vmovdqu64 YMMWORD PTR [rbx+1216], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+480]
	vmovdqu64 YMMWORD PTR [rbx+1248], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+512]
	vmovdqu64 YMMWORD PTR [rbx+1280], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10624]
	vmovdqu64 YMMWORD PTR [rbx+11392], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10656]
	vmovdqu64 YMMWORD PTR [rbx+11424], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10688]
	vmovdqu64 YMMWORD PTR [rbx+11456], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10720]
	vmovdqu64 YMMWORD PTR [rbx+11488], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10752]
	vmovdqu64 YMMWORD PTR [rbx+11520], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10784]
	vmovdqu64 YMMWORD PTR [rbx+11552], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10816]
	vmovdqu64 YMMWORD PTR [rbx+11584], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10848]
	vmovdqu64 YMMWORD PTR [rbx+11616], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+544]
	vmovdqu64 YMMWORD PTR [rbx+1312], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+576]
	vmovdqu64 YMMWORD PTR [rbx+1344], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+608]
	vmovdqu64 YMMWORD PTR [rbx+1376], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+640]
	vmovdqu64 YMMWORD PTR [rbx+1408], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+672]
	vmovdqu64 YMMWORD PTR [rbx+1440], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+704]
	vmovdqu64 YMMWORD PTR [rbx+1472], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+736]
	vmovdqu64 YMMWORD PTR [rbx+1504], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+768]
	vmovdqu64 YMMWORD PTR [rbx+1536], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10880]
	vmovdqu64 YMMWORD PTR [rbx+11648], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10912]
	vmovdqu64 YMMWORD PTR [rbx+11680], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10944]
	vmovdqu64 YMMWORD PTR [rbx+11712], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10976]
	vmovdqu64 YMMWORD PTR [rbx+11744], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+11008]
	vmovdqu64 YMMWORD PTR [rbx+11776], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+11040]
	vmovdqu64 YMMWORD PTR [rbx+11808], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+11072]
	vmovdqu64 YMMWORD PTR [rbx+11840], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+11104]
	vmovdqu64 YMMWORD PTR [rbx+11872], ymm0
237:
	add r13, 256
	cmp r13, 9248
	jne 232b
	mov r13d, 4
238:
	cmp r13, 312
	je 239f
	movzx eax, BYTE PTR [rbx+r13*1+9472]
	mov QWORD PTR [rbx+10048], rax
	movzx eax, BYTE PTR [rbx+r13*1+19808]
	mov QWORD PTR [rbx+20384], rax
	mov r8, rbx
	add r8, 1056
	mov rdx, QWORD PTR [rbx+10048]
	mov ecx, 0
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
241:
	mov rax, rcx
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	vmovq xmm8, rax
	vpbroadcastq ymm8, xmm8
	vmovdqu64 ymm9, YMMWORD PTR [r8]
	vpternlogq ymm0, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+32]
	vpternlogq ymm1, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+64]
	vpternlogq ymm2, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+96]
	vpternlogq ymm3, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+128]
	vpternlogq ymm4, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+160]
	vpternlogq ymm5, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+192]
	vpternlogq ymm6, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+224]
	vpternlogq ymm7, ymm9, ymm8, 248
	add r8, 256
	add rcx, 1
	cmp rcx, 32
	jne 241b
	vmovdqu64 YMMWORD PTR [rbx+800], ymm0
	vmovdqu64 YMMWORD PTR [rbx+832], ymm1
	vmovdqu64 YMMWORD PTR [rbx+864], ymm2
	vmovdqu64 YMMWORD PTR [rbx+896], ymm3
	vmovdqu64 YMMWORD PTR [rbx+928], ymm4
	vmovdqu64 YMMWORD PTR [rbx+960], ymm5
	vmovdqu64 YMMWORD PTR [rbx+992], ymm6
	vmovdqu64 YMMWORD PTR [rbx+1024], ymm7
	mov r8, rbx
	add r8, 11392
	mov rdx, QWORD PTR [rbx+20384]
	mov ecx, 0
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
242:
	mov rax, rcx
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	vmovq xmm8, rax
	vpbroadcastq ymm8, xmm8
	vmovdqu64 ymm9, YMMWORD PTR [r8]
	vpternlogq ymm0, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+32]
	vpternlogq ymm1, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+64]
	vpternlogq ymm2, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+96]
	vpternlogq ymm3, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+128]
	vpternlogq ymm4, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+160]
	vpternlogq ymm5, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+192]
	vpternlogq ymm6, ymm9, ymm8, 248
	vmovdqu64 ymm9, YMMWORD PTR [r8+224]
	vpternlogq ymm7, ymm9, ymm8, 248
	add r8, 256
	add rcx, 1
	cmp rcx, 32
	jne 242b
	vmovdqu64 YMMWORD PTR [rbx+11136], ymm0
	vmovdqu64 YMMWORD PTR [rbx+11168], ymm1
	vmovdqu64 YMMWORD PTR [rbx+11200], ymm2
	vmovdqu64 YMMWORD PTR [rbx+11232], ymm3
	vmovdqu64 YMMWORD PTR [rbx+11264], ymm4
	vmovdqu64 YMMWORD PTR [rbx+11296], ymm5
	vmovdqu64 YMMWORD PTR [rbx+11328], ymm6
	vmovdqu64 YMMWORD PTR [rbx+11360], ymm7
	mov r15d, 6
	jmp 240f
239:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10080]
	vmovdqu64 YMMWORD PTR [rbx+800], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10112]
	vmovdqu64 YMMWORD PTR [rbx+832], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10144]
	vmovdqu64 YMMWORD PTR [rbx+864], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10176]
	vmovdqu64 YMMWORD PTR [rbx+896], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10208]
	vmovdqu64 YMMWORD PTR [rbx+928], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10240]
	vmovdqu64 YMMWORD PTR [rbx+960], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10272]
	vmovdqu64 YMMWORD PTR [rbx+992], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10304]
	vmovdqu64 YMMWORD PTR [rbx+1024], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20416]
	vmovdqu64 YMMWORD PTR [rbx+11136], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20448]
	vmovdqu64 YMMWORD PTR [rbx+11168], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20480]
	vmovdqu64 YMMWORD PTR [rbx+11200], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20512]
	vmovdqu64 YMMWORD PTR [rbx+11232], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20544]
	vmovdqu64 YMMWORD PTR [rbx+11264], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20576]
	vmovdqu64 YMMWORD PTR [rbx+11296], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20608]
	vmovdqu64 YMMWORD PTR [rbx+11328], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+20640]
	vmovdqu64 YMMWORD PTR [rbx+11360], ymm0
	mov r15d, 1
240:
243:
	cmp r15, 1
	je 244f
	mov r8, rbx
	add r8, 288
	mov r9, rbx
	add r9, 288
	mov r11, rbx
	add r11, 288
	jmp 245f
244:
	mov r8, rbx
	add r8, 288
	mov r9, rbx
	add r9, 800
	mov r11, rbx
	add r11, 288
245:
	mov r10, rbx
	mov ecx, 3
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpxorq ymm8, ymm8, ymm8
	vpxorq ymm9, ymm9, ymm9
	vpxorq ymm10, ymm10, ymm10
	vpxorq ymm11, ymm11, ymm11
	vpxorq ymm12, ymm12, ymm12
	vpxorq ymm13, ymm13, ymm13
	vpxorq ymm14, ymm14, ymm14
	vpxorq ymm15, ymm15, ymm15
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpxorq ymm19, ymm19, ymm19
	vpxorq ymm20, ymm20, ymm20
246:
	mov rax, QWORD PTR [r9]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10336]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm0, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm8, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm0, 52
	vmovq xmm21, xmm21
	vpaddq ymm1, ymm1, ymm21
	valignq ymm0, ymm20, ymm0, 1
	vpsrlq ymm21, ymm8, 52
	vmovq xmm21, xmm21
	vpaddq ymm9, ymm9, ymm21
	valignq ymm8, ymm20, ymm8, 1
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10368]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm1, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm9, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm1, 52
	vmovq xmm21, xmm21
	vpaddq ymm2, ymm2, ymm21
	valignq ymm1, ymm20, ymm1, 1
	vpsrlq ymm21, ymm9, 52
	vmovq xmm21, xmm21
	vpaddq ymm10, ymm10, ymm21
	valignq ymm9, ymm20, ymm9, 1
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10400]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm2, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm10, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm2, 52
	vmovq xmm21, xmm21
	vpaddq ymm3, ymm3, ymm21
	valignq ymm2, ymm20, ymm2, 1
	vpsrlq ymm21, ymm10, 52
	vmovq xmm21, xmm21
	vpaddq ymm11, ymm11, ymm21
	valignq ymm10, ymm20, ymm10, 1
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10432]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm3, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm11, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm3, 52
	vmovq xmm21, xmm21
	vpaddq ymm4, ymm4, ymm21
	valignq ymm3, ymm20, ymm3, 1
	vpsrlq ymm21, ymm11, 52
	vmovq xmm21, xmm21
	vpaddq ymm12, ymm12, ymm21
	valignq ymm11, ymm20, ymm11, 1
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10464]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm4, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm12, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm4, 52
	vmovq xmm21, xmm21
	vpaddq ymm5, ymm5, ymm21
	valignq ymm4, ymm20, ymm4, 1
	vpsrlq ymm21, ymm12, 52
	vmovq xmm21, xmm21
	vpaddq ymm13, ymm13, ymm21
	valignq ymm12, ymm20, ymm12, 1
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10496]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm5, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm13, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm5, 52
	vmovq xmm21, xmm21
	vpaddq ymm6, ymm6, ymm21
	valignq ymm5, ymm20, ymm5, 1
	vpsrlq ymm21, ymm13, 52
	vmovq xmm21, xmm21
	vpaddq ymm14, ymm14, ymm21
	valignq ymm13, ymm20, ymm13, 1
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10528]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm6, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm14, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm6, 52
	vmovq xmm21, xmm21
	vpaddq ymm7, ymm7, ymm21
	valignq ymm6, ymm20, ymm6, 1
	vpsrlq ymm21, ymm14, 52
	vmovq xmm21, xmm21
	vpaddq ymm15, ymm15, ymm21
	valignq ymm14, ymm20, ymm14, 1
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10560]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm7, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm15, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm7, 52
	vmovq xmm21, xmm21
	vpaddq ymm0, ymm0, ymm21
	valignq ymm7, ymm20, ymm7, 1
	vpsrlq ymm21, ymm15, 52
	vmovq xmm21, xmm21
	vpaddq ymm8, ymm8, ymm21
	valignq ymm15, ymm20, ymm15, 1
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10560]
	add r9, 8
	sub rcx, 1
	jne 246b
	mov rax, QWORD PTR [r9]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10336]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm0, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm8, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm0, 52
	vmovq xmm21, xmm21
	vpaddq ymm1, ymm1, ymm21
	valignq ymm0, ymm20, ymm0, 1
	vpsrlq ymm21, ymm8, 52
	vmovq xmm21, xmm21
	vpaddq ymm9, ymm9, ymm21
	valignq ymm8, ymm20, ymm8, 1
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10368]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm1, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm9, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm1, 52
	vmovq xmm21, xmm21
	vpaddq ymm2, ymm2, ymm21
	valignq ymm1, ymm20, ymm1, 1
	vpsrlq ymm21, ymm9, 52
	vmovq xmm21, xmm21
	vpaddq ymm10, ymm10, ymm21
	valignq ymm9, ymm20, ymm9, 1
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10400]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm2, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm10, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm2, 52
	vmovq xmm21, xmm21
	vpaddq ymm3, ymm3, ymm21
	valignq ymm2, ymm20, ymm2, 1
	vpsrlq ymm21, ymm10, 52
	vmovq xmm21, xmm21
	vpaddq ymm11, ymm11, ymm21
	valignq ymm10, ymm20, ymm10, 1
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10432]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm3, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm11, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm3, 52
	vmovq xmm21, xmm21
	vpaddq ymm4, ymm4, ymm21
	valignq ymm3, ymm20, ymm3, 1
	vpsrlq ymm21, ymm11, 52
	vmovq xmm21, xmm21
	vpaddq ymm12, ymm12, ymm21
	valignq ymm11, ymm20, ymm11, 1
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10464]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm4, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm12, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm4, 52
	vmovq xmm21, xmm21
	vpaddq ymm5, ymm5, ymm21
	valignq ymm4, ymm20, ymm4, 1
	vpsrlq ymm21, ymm12, 52
	vmovq xmm21, xmm21
	vpaddq ymm13, ymm13, ymm21
	valignq ymm12, ymm20, ymm12, 1
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10560]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm16, rax
	vpbroadcastq ymm16, xmm16
	mov rax, QWORD PTR [r9+10496]
	vmovq xmm17, rax
	vpbroadcastq ymm17, xmm17
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm14, ymm17, YMMWORD PTR [r8+10368]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm5, YMMWORD PTR [r10+256]
	vpbroadcastq ymm18, xmm21
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm13, YMMWORD PTR [r10+10592]
	vpbroadcastq ymm19, xmm21
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm18, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm18, YMMWORD PTR [r10+32]
	vpmadd52huq ymm14, ymm17, YMMWORD PTR [r8+10336]
	vpmadd52luq ymm13, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm14, ymm19, YMMWORD PTR [r10+10368]
	vpsrlq ymm21, ymm5, 52
	vmovq xmm21, xmm21
	vpaddq ymm6, ymm6, ymm21
	valignq ymm5, ymm20, ymm5, 1
	vpsrlq ymm21, ymm13, 52
	vmovq xmm21, xmm21
	vpaddq ymm14, ymm14, ymm21
	valignq ymm13, ymm20, ymm13, 1
	vpmadd52huq ymm6, ymm18, YMMWORD PTR [r10]
	vpmadd52huq ymm14, ymm19, YMMWORD PTR [r10+10336]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm18, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm18, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm18, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm18, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm18, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm18, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm18, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm18, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm18, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm18, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm18, YMMWORD PTR [r10+192]
	vpmadd52luq ymm15, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52huq ymm15, ymm17, YMMWORD PTR [r8+10368]
	vpmadd52luq ymm15, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52huq ymm15, ymm19, YMMWORD PTR [r10+10368]
	vpmadd52luq ymm8, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52huq ymm8, ymm17, YMMWORD PTR [r8+10400]
	vpmadd52luq ymm8, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52huq ymm8, ymm19, YMMWORD PTR [r10+10400]
	vpmadd52luq ymm9, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52huq ymm9, ymm17, YMMWORD PTR [r8+10432]
	vpmadd52luq ymm9, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52huq ymm9, ymm19, YMMWORD PTR [r10+10432]
	vpmadd52luq ymm10, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52huq ymm10, ymm17, YMMWORD PTR [r8+10464]
	vpmadd52luq ymm10, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52huq ymm10, ymm19, YMMWORD PTR [r10+10464]
	vpmadd52luq ymm11, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r8+10496]
	vpmadd52luq ymm11, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm11, ymm19, YMMWORD PTR [r10+10496]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r8+10528]
	vpmadd52luq ymm12, ymm19, YMMWORD PTR [r10+10560]
	vpmadd52huq ymm12, ymm19, YMMWORD PTR [r10+10528]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm18, YMMWORD PTR [r10+224]
	vpmadd52huq ymm13, ymm17, YMMWORD PTR [r8+10560]
	vpmadd52huq ymm13, ymm19, YMMWORD PTR [r10+10560]
	movabs r12, 4503599627370495
	vmovq xmm24, r12
	vpbroadcastq ymm24, xmm24
	mov eax, 1
	vmovq xmm25, rax
	vpbroadcastq ymm25, xmm25
	vpxorq ymm26, ymm26, ymm26
	mov esi, 16843009
	vpsrlq ymm16, ymm6, 52
	vpandq ymm6, ymm6, ymm24
	vpsrlq ymm17, ymm7, 52
	vpandq ymm7, ymm7, ymm24
	vpsrlq ymm18, ymm0, 52
	vpandq ymm0, ymm0, ymm24
	vpsrlq ymm19, ymm1, 52
	vpandq ymm1, ymm1, ymm24
	vpsrlq ymm20, ymm2, 52
	vpandq ymm2, ymm2, ymm24
	vpsrlq ymm21, ymm3, 52
	vpandq ymm3, ymm3, ymm24
	vpsrlq ymm22, ymm4, 52
	vpandq ymm4, ymm4, ymm24
	vpsrlq ymm23, ymm5, 52
	vpandq ymm5, ymm5, ymm24
	valignq ymm27, ymm23, ymm26, 3
	xor eax, eax
	xor ecx, ecx
	vpaddq ymm6, ymm6, ymm27
	vpcmpuq k1, ymm6, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	or eax, edx
	vpcmpuq k1, ymm6, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	or ecx, edx
	vpaddq ymm7, ymm7, ymm16
	vpcmpuq k1, ymm7, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 1
	or eax, edx
	vpcmpuq k1, ymm7, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 1
	or ecx, edx
	vpaddq ymm0, ymm0, ymm17
	vpcmpuq k1, ymm0, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 2
	or eax, edx
	vpcmpuq k1, ymm0, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 2
	or ecx, edx
	vpaddq ymm1, ymm1, ymm18
	vpcmpuq k1, ymm1, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 3
	or eax, edx
	vpcmpuq k1, ymm1, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 3
	or ecx, edx
	vpaddq ymm2, ymm2, ymm19
	vpcmpuq k1, ymm2, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 4
	or eax, edx
	vpcmpuq k1, ymm2, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 4
	or ecx, edx
	vpaddq ymm3, ymm3, ymm20
	vpcmpuq k1, ymm3, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 5
	or eax, edx
	vpcmpuq k1, ymm3, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 5
	or ecx, edx
	vpaddq ymm4, ymm4, ymm21
	vpcmpuq k1, ymm4, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 6
	or eax, edx
	vpcmpuq k1, ymm4, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 6
	or ecx, edx
	vpaddq ymm5, ymm5, ymm22
	vpcmpuq k1, ymm5, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 7
	or eax, edx
	vpcmpuq k1, ymm5, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 7
	or ecx, edx
	shl rax, 1
	add rax, rcx
	xor rax, rcx
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm6 {k1}, ymm6, ymm25
	kxorw k1, k1, k1
	vpandq ymm6, ymm6, ymm24
	vmovdqu64 YMMWORD PTR [r11], ymm6
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm7 {k1}, ymm7, ymm25
	kxorw k1, k1, k1
	vpandq ymm7, ymm7, ymm24
	vmovdqu64 YMMWORD PTR [r11+32], ymm7
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm0 {k1}, ymm0, ymm25
	kxorw k1, k1, k1
	vpandq ymm0, ymm0, ymm24
	vmovdqu64 YMMWORD PTR [r11+64], ymm0
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm1 {k1}, ymm1, ymm25
	kxorw k1, k1, k1
	vpandq ymm1, ymm1, ymm24
	vmovdqu64 YMMWORD PTR [r11+96], ymm1
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm2 {k1}, ymm2, ymm25
	kxorw k1, k1, k1
	vpandq ymm2, ymm2, ymm24
	vmovdqu64 YMMWORD PTR [r11+128], ymm2
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm3 {k1}, ymm3, ymm25
	kxorw k1, k1, k1
	vpandq ymm3, ymm3, ymm24
	vmovdqu64 YMMWORD PTR [r11+160], ymm3
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm4 {k1}, ymm4, ymm25
	kxorw k1, k1, k1
	vpandq ymm4, ymm4, ymm24
	vmovdqu64 YMMWORD PTR [r11+192], ymm4
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm5 {k1}, ymm5, ymm25
	kxorw k1, k1, k1
	vpandq ymm5, ymm5, ymm24
	vmovdqu64 YMMWORD PTR [r11+224], ymm5
	shr rax, 25
	vpermq ymm6, ymm23, 255
	movq rdx, xmm6
	add rdx, rax
	mov r10, rdx
	vpsrlq ymm16, ymm14, 52
	vpandq ymm14, ymm14, ymm24
	vpsrlq ymm17, ymm15, 52
	vpandq ymm15, ymm15, ymm24
	vpsrlq ymm18, ymm8, 52
	vpandq ymm8, ymm8, ymm24
	vpsrlq ymm19, ymm9, 52
	vpandq ymm9, ymm9, ymm24
	vpsrlq ymm20, ymm10, 52
	vpandq ymm10, ymm10, ymm24
	vpsrlq ymm21, ymm11, 52
	vpandq ymm11, ymm11, ymm24
	vpsrlq ymm22, ymm12, 52
	vpandq ymm12, ymm12, ymm24
	vpsrlq ymm23, ymm13, 52
	vpandq ymm13, ymm13, ymm24
	valignq ymm27, ymm23, ymm26, 3
	xor eax, eax
	xor ecx, ecx
	vpaddq ymm14, ymm14, ymm27
	vpcmpuq k1, ymm14, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	or eax, edx
	vpcmpuq k1, ymm14, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	or ecx, edx
	vpaddq ymm15, ymm15, ymm16
	vpcmpuq k1, ymm15, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 1
	or eax, edx
	vpcmpuq k1, ymm15, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 1
	or ecx, edx
	vpaddq ymm8, ymm8, ymm17
	vpcmpuq k1, ymm8, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 2
	or eax, edx
	vpcmpuq k1, ymm8, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 2
	or ecx, edx
	vpaddq ymm9, ymm9, ymm18
	vpcmpuq k1, ymm9, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 3
	or eax, edx
	vpcmpuq k1, ymm9, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 3
	or ecx, edx
	vpaddq ymm10, ymm10, ymm19
	vpcmpuq k1, ymm10, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 4
	or eax, edx
	vpcmpuq k1, ymm10, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 4
	or ecx, edx
	vpaddq ymm11, ymm11, ymm20
	vpcmpuq k1, ymm11, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 5
	or eax, edx
	vpcmpuq k1, ymm11, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 5
	or ecx, edx
	vpaddq ymm12, ymm12, ymm21
	vpcmpuq k1, ymm12, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 6
	or eax, edx
	vpcmpuq k1, ymm12, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 6
	or ecx, edx
	vpaddq ymm13, ymm13, ymm22
	vpcmpuq k1, ymm13, ymm24, 6
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 7
	or eax, edx
	vpcmpuq k1, ymm13, ymm24, 0
	kmovw edx, k1
	kxorw k1, k1, k1
	imul rdx, rdx, 2113665
	and rdx, rsi
	shl edx, 7
	or ecx, edx
	shl rax, 1
	add rax, rcx
	xor rax, rcx
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm14 {k1}, ymm14, ymm25
	kxorw k1, k1, k1
	vpandq ymm14, ymm14, ymm24
	vmovdqu64 YMMWORD PTR [r11+10336], ymm14
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm15 {k1}, ymm15, ymm25
	kxorw k1, k1, k1
	vpandq ymm15, ymm15, ymm24
	vmovdqu64 YMMWORD PTR [r11+10368], ymm15
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm8 {k1}, ymm8, ymm25
	kxorw k1, k1, k1
	vpandq ymm8, ymm8, ymm24
	vmovdqu64 YMMWORD PTR [r11+10400], ymm8
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm9 {k1}, ymm9, ymm25
	kxorw k1, k1, k1
	vpandq ymm9, ymm9, ymm24
	vmovdqu64 YMMWORD PTR [r11+10432], ymm9
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm10 {k1}, ymm10, ymm25
	kxorw k1, k1, k1
	vpandq ymm10, ymm10, ymm24
	vmovdqu64 YMMWORD PTR [r11+10464], ymm10
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm11 {k1}, ymm11, ymm25
	kxorw k1, k1, k1
	vpandq ymm11, ymm11, ymm24
	vmovdqu64 YMMWORD PTR [r11+10496], ymm11
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm12 {k1}, ymm12, ymm25
	kxorw k1, k1, k1
	vpandq ymm12, ymm12, ymm24
	vmovdqu64 YMMWORD PTR [r11+10528], ymm12
	shr rax, 1
	mov rdx, rax
	and rdx, rsi
	imul rdx, rdx, 16909320
	shr rdx, 24
	and rdx, 15
	kmovw k1, edx
	vpaddq ymm13 {k1}, ymm13, ymm25
	kxorw k1, k1, k1
	vpandq ymm13, ymm13, ymm24
	vmovdqu64 YMMWORD PTR [r11+10560], ymm13
	shr rax, 25
	vpermq ymm14, ymm23, 255
	movq rsi, xmm14
	add rsi, rax
	mov rdx, r10
	sub r15, 1
	jne 243b
	add r13, 1
	cmp r13, 313
	jne 238b
	vzeroupper
	mov r11, QWORD PTR [rdi+232]
	add r11, 10624
	mov r8, QWORD PTR [rdi+80]
	mov eax, 0
	mov rcx, QWORD PTR [r11]
	or rax, rcx
	mov rcx, QWORD PTR [r11+32]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+32]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+64]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+64]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+96]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+16], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+96]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+128]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+24], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+128]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+160]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+192]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+32], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+192]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+224]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+40], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+224]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+48], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+8]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+40]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+56], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+40]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+136]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+168]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+168]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+200]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+200]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+232]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+16]
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+48]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+80]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+80]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+112]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+144]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+208]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+136], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+208]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+240]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+144], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+240]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+152], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+24]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+56]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+160], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+56]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+88]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+120]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+168], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+120]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+152]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+176], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+152]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+184]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+184], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+184]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+216]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+192], rax
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
247:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 247b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
248:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 248b
	mov rdi, QWORD PTR [rdi+128]
	mov rdi, QWORD PTR [rdi+232]
	mov r11, QWORD PTR [rdi+232]
	add r11, 288
	mov r8, QWORD PTR [rdi+80]
	mov eax, 0
	mov rcx, QWORD PTR [r11]
	or rax, rcx
	mov rcx, QWORD PTR [r11+32]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+32]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+64]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+8], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+64]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+96]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+16], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+96]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+128]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+24], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+128]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+160]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+192]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+32], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+192]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+224]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+40], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+224]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+48], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+8]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+40]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+56], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+40]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+136]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+168]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+168]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+200]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+200]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+232]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+16]
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+48]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+80]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+80]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+112]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+144]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+208]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+136], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+208]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+240]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+144], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+240]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+152], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+24]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+56]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+160], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+56]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+88]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+120]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+168], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+120]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+152]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+176], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+152]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+184]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+184], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+184]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+216]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+192], rax
	mov rbx, QWORD PTR [rdi+112]
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+88]
	mov ebp, 0
	mov r14, 0
249:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 249b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
250:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 250b
	mov rdi, QWORD PTR [rdi+128]
	ret
	.p2align 6
