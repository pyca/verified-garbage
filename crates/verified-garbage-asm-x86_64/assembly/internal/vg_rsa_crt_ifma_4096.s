// The functions of `src/internal/vg_rsa_crt_ifma_4096.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_crt_ifma_4096:
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
	mov ecx, 64
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
	add r11, 12608
	movabs r12, 4503599627370495
	jmp 213f
212:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 352
	movabs r12, 4503599627370495
213:
	jmp 211f
210:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 672
	movabs r12, 4503599627370495
211:
	jmp 29f
28:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 12256
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
	mov QWORD PTR [r11+256], rax
	mov rax, QWORD PTR [rsi+56]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+64]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+288], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+192]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	mov rax, QWORD PTR [rsi+192]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+200]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+200]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+208]
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+208]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+216]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+216]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+224]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+224]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+232]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov rax, QWORD PTR [rsi+232]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+240]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+248], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+248]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	mov rax, QWORD PTR [rsi+248]
	shr rax, 44
	and rax, r12
	mov QWORD PTR [r11+312], rax
	sub r8, 1
	jne 25b
	mov r11, QWORD PTR [rdi+232]
	add r11, 0
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [r11+320], rax
	mov QWORD PTR [r11+328], rax
	mov QWORD PTR [r11+336], rax
	mov QWORD PTR [r11+344], rax
	mov eax, 0
	mov QWORD PTR [r11+11552], rax
	mov QWORD PTR [r11+11560], rax
	mov QWORD PTR [r11+11568], rax
	mov QWORD PTR [r11+11576], rax
	mov QWORD PTR [r11+11584], rax
	mov QWORD PTR [r11+11592], rax
	mov QWORD PTR [r11+11600], rax
	mov QWORD PTR [r11+11608], rax
	mov QWORD PTR [r11+11616], rax
	mov QWORD PTR [r11+11624], rax
	mov QWORD PTR [r11+11632], rax
	mov QWORD PTR [r11+11640], rax
	mov QWORD PTR [r11+11648], rax
	mov QWORD PTR [r11+11656], rax
	mov QWORD PTR [r11+11664], rax
	mov QWORD PTR [r11+11672], rax
	mov QWORD PTR [r11+11680], rax
	mov QWORD PTR [r11+11688], rax
	mov QWORD PTR [r11+11696], rax
	mov QWORD PTR [r11+11704], rax
	mov QWORD PTR [r11+11712], rax
	mov QWORD PTR [r11+11720], rax
	mov QWORD PTR [r11+11728], rax
	mov QWORD PTR [r11+11736], rax
	mov QWORD PTR [r11+11744], rax
	mov QWORD PTR [r11+11752], rax
	mov QWORD PTR [r11+11760], rax
	mov QWORD PTR [r11+11768], rax
	mov QWORD PTR [r11+11776], rax
	mov QWORD PTR [r11+11784], rax
	mov QWORD PTR [r11+11792], rax
	mov QWORD PTR [r11+11800], rax
	mov QWORD PTR [r11+11808], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+200]
	mov rcx, QWORD PTR [rax+160]
	add r11, 11812
	sub r11, rcx
214:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 214b
	mov r8, QWORD PTR [rdi+232]
	add r8, 11552
	mov r9, QWORD PTR [rdi+232]
	add r9, 11840
	mov ecx, 52
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
	mov ecx, 64
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
	add r11, 25536
	movabs r12, 4503599627370495
	jmp 229f
228:
	mov rsi, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+232]
	add r11, 13280
	movabs r12, 4503599627370495
229:
	jmp 227f
226:
	mov rsi, QWORD PTR [rdi+96]
	mov r11, QWORD PTR [rdi+232]
	add r11, 13600
	movabs r12, 4503599627370495
227:
	jmp 225f
224:
	mov rsi, QWORD PTR [rdi+104]
	mov r11, QWORD PTR [rdi+232]
	add r11, 25184
	movabs r12, 4503599627370495
225:
	jmp 223f
222:
	mov rsi, QWORD PTR [rdi+64]
	mov r11, QWORD PTR [rdi+232]
	add r11, 12928
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
	mov QWORD PTR [r11+256], rax
	mov rax, QWORD PTR [rsi+56]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+64]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+288], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+8], rax
	mov rax, QWORD PTR [rsi+64]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+72]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	mov rax, QWORD PTR [rsi+72]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+80]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	mov rax, QWORD PTR [rsi+80]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+88]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	mov rax, QWORD PTR [rsi+88]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+96]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	mov rax, QWORD PTR [rsi+96]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+168], rax
	mov rax, QWORD PTR [rsi+104]
	and rax, r12
	mov QWORD PTR [r11+200], rax
	mov rax, QWORD PTR [rsi+104]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+112]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	mov rax, QWORD PTR [rsi+112]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+120]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	mov rax, QWORD PTR [rsi+120]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+128]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	mov rax, QWORD PTR [rsi+128]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+136]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [rsi+136]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+144]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	mov rax, QWORD PTR [rsi+144]
	shr rax, 44
	mov rcx, QWORD PTR [rsi+152]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	mov rax, QWORD PTR [rsi+152]
	shr rax, 32
	mov rcx, QWORD PTR [rsi+160]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	mov rax, QWORD PTR [rsi+160]
	shr rax, 20
	mov rcx, QWORD PTR [rsi+168]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 8
	and rax, r12
	mov QWORD PTR [r11+208], rax
	mov rax, QWORD PTR [rsi+168]
	shr rax, 60
	mov rcx, QWORD PTR [rsi+176]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	mov rax, QWORD PTR [rsi+176]
	shr rax, 48
	mov rcx, QWORD PTR [rsi+184]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	mov rax, QWORD PTR [rsi+184]
	shr rax, 36
	mov rcx, QWORD PTR [rsi+192]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	mov rax, QWORD PTR [rsi+192]
	shr rax, 24
	mov rcx, QWORD PTR [rsi+200]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	mov rax, QWORD PTR [rsi+200]
	shr rax, 12
	and rax, r12
	mov QWORD PTR [r11+56], rax
	mov rax, QWORD PTR [rsi+208]
	and rax, r12
	mov QWORD PTR [r11+88], rax
	mov rax, QWORD PTR [rsi+208]
	shr rax, 52
	mov rcx, QWORD PTR [rsi+216]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	mov rax, QWORD PTR [rsi+216]
	shr rax, 40
	mov rcx, QWORD PTR [rsi+224]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	mov rax, QWORD PTR [rsi+224]
	shr rax, 28
	mov rcx, QWORD PTR [rsi+232]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	mov rax, QWORD PTR [rsi+232]
	shr rax, 16
	mov rcx, QWORD PTR [rsi+240]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 4
	and rax, r12
	mov QWORD PTR [r11+248], rax
	mov rax, QWORD PTR [rsi+240]
	shr rax, 56
	mov rcx, QWORD PTR [rsi+248]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	mov rax, QWORD PTR [rsi+248]
	shr rax, 44
	and rax, r12
	mov QWORD PTR [r11+312], rax
	sub r8, 1
	jne 221b
	mov r11, QWORD PTR [rdi+232]
	add r11, 12928
	mov rax, QWORD PTR [rdi+56]
	and rax, r12
	mov QWORD PTR [r11+320], rax
	mov QWORD PTR [r11+328], rax
	mov QWORD PTR [r11+336], rax
	mov QWORD PTR [r11+344], rax
	mov eax, 0
	mov QWORD PTR [r11+11552], rax
	mov QWORD PTR [r11+11560], rax
	mov QWORD PTR [r11+11568], rax
	mov QWORD PTR [r11+11576], rax
	mov QWORD PTR [r11+11584], rax
	mov QWORD PTR [r11+11592], rax
	mov QWORD PTR [r11+11600], rax
	mov QWORD PTR [r11+11608], rax
	mov QWORD PTR [r11+11616], rax
	mov QWORD PTR [r11+11624], rax
	mov QWORD PTR [r11+11632], rax
	mov QWORD PTR [r11+11640], rax
	mov QWORD PTR [r11+11648], rax
	mov QWORD PTR [r11+11656], rax
	mov QWORD PTR [r11+11664], rax
	mov QWORD PTR [r11+11672], rax
	mov QWORD PTR [r11+11680], rax
	mov QWORD PTR [r11+11688], rax
	mov QWORD PTR [r11+11696], rax
	mov QWORD PTR [r11+11704], rax
	mov QWORD PTR [r11+11712], rax
	mov QWORD PTR [r11+11720], rax
	mov QWORD PTR [r11+11728], rax
	mov QWORD PTR [r11+11736], rax
	mov QWORD PTR [r11+11744], rax
	mov QWORD PTR [r11+11752], rax
	mov QWORD PTR [r11+11760], rax
	mov QWORD PTR [r11+11768], rax
	mov QWORD PTR [r11+11776], rax
	mov QWORD PTR [r11+11784], rax
	mov QWORD PTR [r11+11792], rax
	mov QWORD PTR [r11+11800], rax
	mov QWORD PTR [r11+11808], rax
	mov QWORD PTR [r11+12608], rax
	mov QWORD PTR [r11+12640], rax
	mov QWORD PTR [r11+12672], rax
	mov QWORD PTR [r11+12704], rax
	mov QWORD PTR [r11+12736], rax
	mov QWORD PTR [r11+12768], rax
	mov QWORD PTR [r11+12800], rax
	mov QWORD PTR [r11+12832], rax
	mov QWORD PTR [r11+12864], rax
	mov QWORD PTR [r11+12896], rax
	mov QWORD PTR [r11+12616], rax
	mov QWORD PTR [r11+12648], rax
	mov QWORD PTR [r11+12680], rax
	mov QWORD PTR [r11+12712], rax
	mov QWORD PTR [r11+12744], rax
	mov QWORD PTR [r11+12776], rax
	mov QWORD PTR [r11+12808], rax
	mov QWORD PTR [r11+12840], rax
	mov QWORD PTR [r11+12872], rax
	mov QWORD PTR [r11+12904], rax
	mov QWORD PTR [r11+12624], rax
	mov QWORD PTR [r11+12656], rax
	mov QWORD PTR [r11+12688], rax
	mov QWORD PTR [r11+12720], rax
	mov QWORD PTR [r11+12752], rax
	mov QWORD PTR [r11+12784], rax
	mov QWORD PTR [r11+12816], rax
	mov QWORD PTR [r11+12848], rax
	mov QWORD PTR [r11+12880], rax
	mov QWORD PTR [r11+12912], rax
	mov QWORD PTR [r11+12632], rax
	mov QWORD PTR [r11+12664], rax
	mov QWORD PTR [r11+12696], rax
	mov QWORD PTR [r11+12728], rax
	mov QWORD PTR [r11+12760], rax
	mov QWORD PTR [r11+12792], rax
	mov QWORD PTR [r11+12824], rax
	mov QWORD PTR [r11+12856], rax
	mov QWORD PTR [r11+12888], rax
	mov QWORD PTR [r11+12920], rax
	mov eax, 1
	mov QWORD PTR [r11+12608], rax
	mov rax, QWORD PTR [rdi+128]
	mov rsi, QWORD PTR [rax+216]
	mov rcx, QWORD PTR [rax+192]
	add r11, 11812
	sub r11, rcx
230:
	movzx eax, BYTE PTR [rsi]
	mov BYTE PTR [r11], al
	add rsi, 1
	add r11, 1
	sub rcx, 1
	jne 230b
	mov r8, QWORD PTR [rdi+232]
	add r8, 24480
	mov r9, QWORD PTR [rdi+232]
	add r9, 24768
	mov ecx, 52
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
	mov r13d, 1312
232:
	cmp r13, 1952
	jb 233f
	mov r8, rbx
	add r8, r13
	sub r8, 320
	mov r9, rbx
	add r9, 672
	mov r11, rbx
	add r11, r13
	jmp 234f
233:
	mov r8, rbx
	add r8, r13
	sub r8, 960
	mov r9, rbx
	add r9, 12256
	mov r11, r8
234:
	mov r10, rbx
	mov ecx, 4
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
	vpxorq ymm21, ymm21, ymm21
	vpxorq ymm22, ymm22, ymm22
	vpxorq ymm23, ymm23, ymm23
	vpxorq ymm24, ymm24, ymm24
235:
	mov rax, QWORD PTR [r9]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+12928]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm10, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm0, 52
	vmovq xmm25, xmm25
	vpaddq ymm1, ymm1, ymm25
	valignq ymm0, ymm24, ymm0, 1
	vpsrlq ymm25, ymm10, 52
	vmovq xmm25, xmm25
	vpaddq ymm11, ymm11, ymm25
	valignq ymm10, ymm24, ymm10, 1
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+12960]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm11, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm1, 52
	vmovq xmm25, xmm25
	vpaddq ymm2, ymm2, ymm25
	valignq ymm1, ymm24, ymm1, 1
	vpsrlq ymm25, ymm11, 52
	vmovq xmm25, xmm25
	vpaddq ymm12, ymm12, ymm25
	valignq ymm11, ymm24, ymm11, 1
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+12992]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm12, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm2, 52
	vmovq xmm25, xmm25
	vpaddq ymm3, ymm3, ymm25
	valignq ymm2, ymm24, ymm2, 1
	vpsrlq ymm25, ymm12, 52
	vmovq xmm25, xmm25
	vpaddq ymm13, ymm13, ymm25
	valignq ymm12, ymm24, ymm12, 1
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13024]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm13, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm3, 52
	vmovq xmm25, xmm25
	vpaddq ymm4, ymm4, ymm25
	valignq ymm3, ymm24, ymm3, 1
	vpsrlq ymm25, ymm13, 52
	vmovq xmm25, xmm25
	vpaddq ymm14, ymm14, ymm25
	valignq ymm13, ymm24, ymm13, 1
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13056]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm14, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm4, 52
	vmovq xmm25, xmm25
	vpaddq ymm5, ymm5, ymm25
	valignq ymm4, ymm24, ymm4, 1
	vpsrlq ymm25, ymm14, 52
	vmovq xmm25, xmm25
	vpaddq ymm15, ymm15, ymm25
	valignq ymm14, ymm24, ymm14, 1
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13088]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm15, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm5, 52
	vmovq xmm25, xmm25
	vpaddq ymm6, ymm6, ymm25
	valignq ymm5, ymm24, ymm5, 1
	vpsrlq ymm25, ymm15, 52
	vmovq xmm25, xmm25
	vpaddq ymm16, ymm16, ymm25
	valignq ymm15, ymm24, ymm15, 1
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13120]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm16, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm6, 52
	vmovq xmm25, xmm25
	vpaddq ymm7, ymm7, ymm25
	valignq ymm6, ymm24, ymm6, 1
	vpsrlq ymm25, ymm16, 52
	vmovq xmm25, xmm25
	vpaddq ymm17, ymm17, ymm25
	valignq ymm16, ymm24, ymm16, 1
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13152]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm17, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm7, 52
	vmovq xmm25, xmm25
	vpaddq ymm8, ymm8, ymm25
	valignq ymm7, ymm24, ymm7, 1
	vpsrlq ymm25, ymm17, 52
	vmovq xmm25, xmm25
	vpaddq ymm18, ymm18, ymm25
	valignq ymm17, ymm24, ymm17, 1
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+256]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13184]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm8, 52
	vmovq xmm25, xmm25
	vpaddq ymm9, ymm9, ymm25
	valignq ymm8, ymm24, ymm8, 1
	vpsrlq ymm25, ymm18, 52
	vmovq xmm25, xmm25
	vpaddq ymm19, ymm19, ymm25
	valignq ymm18, ymm24, ymm18, 1
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+288]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13216]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm9, 52
	vmovq xmm25, xmm25
	vpaddq ymm0, ymm0, ymm25
	valignq ymm9, ymm24, ymm9, 1
	vpsrlq ymm25, ymm19, 52
	vmovq xmm25, xmm25
	vpaddq ymm10, ymm10, ymm25
	valignq ymm19, ymm24, ymm19, 1
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13216]
	add r9, 8
	sub rcx, 1
	jne 235b
	vmovdqu64 YMMWORD PTR [r11], ymm0
	vmovdqu64 YMMWORD PTR [r11+32], ymm1
	vmovdqu64 YMMWORD PTR [r11+64], ymm2
	vmovdqu64 YMMWORD PTR [r11+96], ymm3
	vmovdqu64 YMMWORD PTR [r11+128], ymm4
	vmovdqu64 YMMWORD PTR [r11+160], ymm5
	vmovdqu64 YMMWORD PTR [r11+192], ymm6
	vmovdqu64 YMMWORD PTR [r11+224], ymm7
	vmovdqu64 YMMWORD PTR [r11+256], ymm8
	vmovdqu64 YMMWORD PTR [r11+288], ymm9
	vmovdqu64 YMMWORD PTR [r11+12928], ymm10
	vmovdqu64 YMMWORD PTR [r11+12960], ymm11
	vmovdqu64 YMMWORD PTR [r11+12992], ymm12
	vmovdqu64 YMMWORD PTR [r11+13024], ymm13
	vmovdqu64 YMMWORD PTR [r11+13056], ymm14
	vmovdqu64 YMMWORD PTR [r11+13088], ymm15
	vmovdqu64 YMMWORD PTR [r11+13120], ymm16
	vmovdqu64 YMMWORD PTR [r11+13152], ymm17
	vmovdqu64 YMMWORD PTR [r11+13184], ymm18
	vmovdqu64 YMMWORD PTR [r11+13216], ymm19
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12928]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12928], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12960]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12960], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12992]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12992], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13024]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13024], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13056]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13056], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13088]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13088], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+192]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13120]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13120], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+224]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13152]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13152], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+256]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+256], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13184]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13184], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+288]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+288], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13216]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13216], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12936]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12936], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12968]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12968], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13000]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13000], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13032]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13032], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13064]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13064], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13096]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13096], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+200]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13128]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13128], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+232]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13160]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13160], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+264]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13192]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13192], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+296]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13224]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13224], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12944]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12944], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12976]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12976], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13008]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13008], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13040]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13040], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13072]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13072], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13104]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13104], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+208]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13136]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13136], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+240]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13168]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13168], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+272]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13200]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13200], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+304]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13232]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13232], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12952]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12952], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12984]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12984], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13016]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13016], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13048]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13048], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13080]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13080], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13112]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13112], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+216]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13144]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13144], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+248]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13176]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13176], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+280]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13208]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13208], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+312]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+312], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13240]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13240], rcx
	shr rsi, 52
	cmp r13, 1632
	je 236f
	jmp 237f
236:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+352]
	vmovdqu64 YMMWORD PTR [rbx+1312], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+384]
	vmovdqu64 YMMWORD PTR [rbx+1344], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+416]
	vmovdqu64 YMMWORD PTR [rbx+1376], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+448]
	vmovdqu64 YMMWORD PTR [rbx+1408], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+480]
	vmovdqu64 YMMWORD PTR [rbx+1440], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+512]
	vmovdqu64 YMMWORD PTR [rbx+1472], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+544]
	vmovdqu64 YMMWORD PTR [rbx+1504], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+576]
	vmovdqu64 YMMWORD PTR [rbx+1536], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+608]
	vmovdqu64 YMMWORD PTR [rbx+1568], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+640]
	vmovdqu64 YMMWORD PTR [rbx+1600], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13280]
	vmovdqu64 YMMWORD PTR [rbx+14240], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13312]
	vmovdqu64 YMMWORD PTR [rbx+14272], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13344]
	vmovdqu64 YMMWORD PTR [rbx+14304], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13376]
	vmovdqu64 YMMWORD PTR [rbx+14336], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13408]
	vmovdqu64 YMMWORD PTR [rbx+14368], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13440]
	vmovdqu64 YMMWORD PTR [rbx+14400], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13472]
	vmovdqu64 YMMWORD PTR [rbx+14432], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13504]
	vmovdqu64 YMMWORD PTR [rbx+14464], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13536]
	vmovdqu64 YMMWORD PTR [rbx+14496], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13568]
	vmovdqu64 YMMWORD PTR [rbx+14528], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+672]
	vmovdqu64 YMMWORD PTR [rbx+1632], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+704]
	vmovdqu64 YMMWORD PTR [rbx+1664], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+736]
	vmovdqu64 YMMWORD PTR [rbx+1696], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+768]
	vmovdqu64 YMMWORD PTR [rbx+1728], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+800]
	vmovdqu64 YMMWORD PTR [rbx+1760], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+832]
	vmovdqu64 YMMWORD PTR [rbx+1792], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+864]
	vmovdqu64 YMMWORD PTR [rbx+1824], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+896]
	vmovdqu64 YMMWORD PTR [rbx+1856], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+928]
	vmovdqu64 YMMWORD PTR [rbx+1888], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+960]
	vmovdqu64 YMMWORD PTR [rbx+1920], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13600]
	vmovdqu64 YMMWORD PTR [rbx+14560], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13632]
	vmovdqu64 YMMWORD PTR [rbx+14592], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13664]
	vmovdqu64 YMMWORD PTR [rbx+14624], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13696]
	vmovdqu64 YMMWORD PTR [rbx+14656], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13728]
	vmovdqu64 YMMWORD PTR [rbx+14688], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13760]
	vmovdqu64 YMMWORD PTR [rbx+14720], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13792]
	vmovdqu64 YMMWORD PTR [rbx+14752], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13824]
	vmovdqu64 YMMWORD PTR [rbx+14784], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13856]
	vmovdqu64 YMMWORD PTR [rbx+14816], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+13888]
	vmovdqu64 YMMWORD PTR [rbx+14848], ymm0
237:
	add r13, 320
	cmp r13, 11552
	jne 232b
	mov r13d, 6
238:
	cmp r13, 416
	je 239f
	movzx eax, BYTE PTR [rbx+r13*1+11840]
	mov QWORD PTR [rbx+12576], rax
	movzx eax, BYTE PTR [rbx+r13*1+24768]
	mov QWORD PTR [rbx+25504], rax
	mov r8, rbx
	add r8, 1312
	mov rdx, QWORD PTR [rbx+12576]
	mov ecx, 0
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
241:
	mov rax, rcx
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vmovdqu64 ymm11, YMMWORD PTR [r8]
	vpternlogq ymm0, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+32]
	vpternlogq ymm1, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+64]
	vpternlogq ymm2, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+96]
	vpternlogq ymm3, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+128]
	vpternlogq ymm4, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+160]
	vpternlogq ymm5, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+192]
	vpternlogq ymm6, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+224]
	vpternlogq ymm7, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+256]
	vpternlogq ymm8, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+288]
	vpternlogq ymm9, ymm11, ymm10, 248
	add r8, 320
	add rcx, 1
	cmp rcx, 32
	jne 241b
	vmovdqu64 YMMWORD PTR [rbx+992], ymm0
	vmovdqu64 YMMWORD PTR [rbx+1024], ymm1
	vmovdqu64 YMMWORD PTR [rbx+1056], ymm2
	vmovdqu64 YMMWORD PTR [rbx+1088], ymm3
	vmovdqu64 YMMWORD PTR [rbx+1120], ymm4
	vmovdqu64 YMMWORD PTR [rbx+1152], ymm5
	vmovdqu64 YMMWORD PTR [rbx+1184], ymm6
	vmovdqu64 YMMWORD PTR [rbx+1216], ymm7
	vmovdqu64 YMMWORD PTR [rbx+1248], ymm8
	vmovdqu64 YMMWORD PTR [rbx+1280], ymm9
	mov r8, rbx
	add r8, 14240
	mov rdx, QWORD PTR [rbx+25504]
	mov ecx, 0
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
242:
	mov rax, rcx
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vmovdqu64 ymm11, YMMWORD PTR [r8]
	vpternlogq ymm0, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+32]
	vpternlogq ymm1, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+64]
	vpternlogq ymm2, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+96]
	vpternlogq ymm3, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+128]
	vpternlogq ymm4, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+160]
	vpternlogq ymm5, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+192]
	vpternlogq ymm6, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+224]
	vpternlogq ymm7, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+256]
	vpternlogq ymm8, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+288]
	vpternlogq ymm9, ymm11, ymm10, 248
	add r8, 320
	add rcx, 1
	cmp rcx, 32
	jne 242b
	vmovdqu64 YMMWORD PTR [rbx+13920], ymm0
	vmovdqu64 YMMWORD PTR [rbx+13952], ymm1
	vmovdqu64 YMMWORD PTR [rbx+13984], ymm2
	vmovdqu64 YMMWORD PTR [rbx+14016], ymm3
	vmovdqu64 YMMWORD PTR [rbx+14048], ymm4
	vmovdqu64 YMMWORD PTR [rbx+14080], ymm5
	vmovdqu64 YMMWORD PTR [rbx+14112], ymm6
	vmovdqu64 YMMWORD PTR [rbx+14144], ymm7
	vmovdqu64 YMMWORD PTR [rbx+14176], ymm8
	vmovdqu64 YMMWORD PTR [rbx+14208], ymm9
	mov r15d, 6
	jmp 240f
239:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12608]
	vmovdqu64 YMMWORD PTR [rbx+992], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12640]
	vmovdqu64 YMMWORD PTR [rbx+1024], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12672]
	vmovdqu64 YMMWORD PTR [rbx+1056], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12704]
	vmovdqu64 YMMWORD PTR [rbx+1088], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12736]
	vmovdqu64 YMMWORD PTR [rbx+1120], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12768]
	vmovdqu64 YMMWORD PTR [rbx+1152], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12800]
	vmovdqu64 YMMWORD PTR [rbx+1184], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12832]
	vmovdqu64 YMMWORD PTR [rbx+1216], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12864]
	vmovdqu64 YMMWORD PTR [rbx+1248], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+12896]
	vmovdqu64 YMMWORD PTR [rbx+1280], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25536]
	vmovdqu64 YMMWORD PTR [rbx+13920], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25568]
	vmovdqu64 YMMWORD PTR [rbx+13952], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25600]
	vmovdqu64 YMMWORD PTR [rbx+13984], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25632]
	vmovdqu64 YMMWORD PTR [rbx+14016], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25664]
	vmovdqu64 YMMWORD PTR [rbx+14048], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25696]
	vmovdqu64 YMMWORD PTR [rbx+14080], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25728]
	vmovdqu64 YMMWORD PTR [rbx+14112], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25760]
	vmovdqu64 YMMWORD PTR [rbx+14144], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25792]
	vmovdqu64 YMMWORD PTR [rbx+14176], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+25824]
	vmovdqu64 YMMWORD PTR [rbx+14208], ymm0
	mov r15d, 1
240:
243:
	cmp r15, 1
	je 244f
	mov r8, rbx
	add r8, 352
	mov r9, rbx
	add r9, 352
	mov r11, rbx
	add r11, 352
	jmp 245f
244:
	mov r8, rbx
	add r8, 352
	mov r9, rbx
	add r9, 992
	mov r11, rbx
	add r11, 352
245:
	mov r10, rbx
	mov ecx, 4
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
	vpxorq ymm21, ymm21, ymm21
	vpxorq ymm22, ymm22, ymm22
	vpxorq ymm23, ymm23, ymm23
	vpxorq ymm24, ymm24, ymm24
246:
	mov rax, QWORD PTR [r9]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+12928]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm10, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm0, 52
	vmovq xmm25, xmm25
	vpaddq ymm1, ymm1, ymm25
	valignq ymm0, ymm24, ymm0, 1
	vpsrlq ymm25, ymm10, 52
	vmovq xmm25, xmm25
	vpaddq ymm11, ymm11, ymm25
	valignq ymm10, ymm24, ymm10, 1
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+12960]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm11, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm1, 52
	vmovq xmm25, xmm25
	vpaddq ymm2, ymm2, ymm25
	valignq ymm1, ymm24, ymm1, 1
	vpsrlq ymm25, ymm11, 52
	vmovq xmm25, xmm25
	vpaddq ymm12, ymm12, ymm25
	valignq ymm11, ymm24, ymm11, 1
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+12992]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm12, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm2, 52
	vmovq xmm25, xmm25
	vpaddq ymm3, ymm3, ymm25
	valignq ymm2, ymm24, ymm2, 1
	vpsrlq ymm25, ymm12, 52
	vmovq xmm25, xmm25
	vpaddq ymm13, ymm13, ymm25
	valignq ymm12, ymm24, ymm12, 1
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13024]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm13, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm3, 52
	vmovq xmm25, xmm25
	vpaddq ymm4, ymm4, ymm25
	valignq ymm3, ymm24, ymm3, 1
	vpsrlq ymm25, ymm13, 52
	vmovq xmm25, xmm25
	vpaddq ymm14, ymm14, ymm25
	valignq ymm13, ymm24, ymm13, 1
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13056]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm14, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm4, 52
	vmovq xmm25, xmm25
	vpaddq ymm5, ymm5, ymm25
	valignq ymm4, ymm24, ymm4, 1
	vpsrlq ymm25, ymm14, 52
	vmovq xmm25, xmm25
	vpaddq ymm15, ymm15, ymm25
	valignq ymm14, ymm24, ymm14, 1
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13088]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm15, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm5, 52
	vmovq xmm25, xmm25
	vpaddq ymm6, ymm6, ymm25
	valignq ymm5, ymm24, ymm5, 1
	vpsrlq ymm25, ymm15, 52
	vmovq xmm25, xmm25
	vpaddq ymm16, ymm16, ymm25
	valignq ymm15, ymm24, ymm15, 1
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13120]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm16, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm6, 52
	vmovq xmm25, xmm25
	vpaddq ymm7, ymm7, ymm25
	valignq ymm6, ymm24, ymm6, 1
	vpsrlq ymm25, ymm16, 52
	vmovq xmm25, xmm25
	vpaddq ymm17, ymm17, ymm25
	valignq ymm16, ymm24, ymm16, 1
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13152]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm17, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm7, 52
	vmovq xmm25, xmm25
	vpaddq ymm8, ymm8, ymm25
	valignq ymm7, ymm24, ymm7, 1
	vpsrlq ymm25, ymm17, 52
	vmovq xmm25, xmm25
	vpaddq ymm18, ymm18, ymm25
	valignq ymm17, ymm24, ymm17, 1
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+256]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13184]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm18, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm8, 52
	vmovq xmm25, xmm25
	vpaddq ymm9, ymm9, ymm25
	valignq ymm8, ymm24, ymm8, 1
	vpsrlq ymm25, ymm18, 52
	vmovq xmm25, xmm25
	vpaddq ymm19, ymm19, ymm25
	valignq ymm18, ymm24, ymm18, 1
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13216]
	mov rax, QWORD PTR [r9+288]
	vmovq xmm20, rax
	vpbroadcastq ymm20, xmm20
	mov rax, QWORD PTR [r9+13216]
	vmovq xmm21, rax
	vpbroadcastq ymm21, xmm21
	vpmadd52luq ymm9, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm19, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm10, ymm21, YMMWORD PTR [r8+12960]
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm22, xmm25
	vpxorq ymm25, ymm25, ymm25
	vpmadd52luq ymm25, ymm19, YMMWORD PTR [r10+13248]
	vpbroadcastq ymm23, xmm25
	vpmadd52huq ymm0, ymm20, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm22, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm22, YMMWORD PTR [r10+32]
	vpmadd52huq ymm10, ymm21, YMMWORD PTR [r8+12928]
	vpmadd52luq ymm19, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm10, ymm23, YMMWORD PTR [r10+12960]
	vpsrlq ymm25, ymm9, 52
	vmovq xmm25, xmm25
	vpaddq ymm0, ymm0, ymm25
	valignq ymm9, ymm24, ymm9, 1
	vpsrlq ymm25, ymm19, 52
	vmovq xmm25, xmm25
	vpaddq ymm10, ymm10, ymm25
	valignq ymm19, ymm24, ymm19, 1
	vpmadd52huq ymm0, ymm22, YMMWORD PTR [r10]
	vpmadd52huq ymm10, ymm23, YMMWORD PTR [r10+12928]
	vpmadd52luq ymm1, ymm20, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm20, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm22, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm22, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm20, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm20, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm22, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm22, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm20, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm20, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm22, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm22, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm20, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm20, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm22, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm22, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm20, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm20, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm22, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm22, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm20, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm20, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm22, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm22, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm20, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm20, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm22, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm20, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm22, YMMWORD PTR [r10+256]
	vpmadd52luq ymm11, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r8+12960]
	vpmadd52luq ymm11, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52huq ymm11, ymm23, YMMWORD PTR [r10+12960]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r8+12992]
	vpmadd52luq ymm12, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52huq ymm12, ymm23, YMMWORD PTR [r10+12992]
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52huq ymm13, ymm21, YMMWORD PTR [r8+13024]
	vpmadd52luq ymm13, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52huq ymm13, ymm23, YMMWORD PTR [r10+13024]
	vpmadd52luq ymm14, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52huq ymm14, ymm21, YMMWORD PTR [r8+13056]
	vpmadd52luq ymm14, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52huq ymm14, ymm23, YMMWORD PTR [r10+13056]
	vpmadd52luq ymm15, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52huq ymm15, ymm21, YMMWORD PTR [r8+13088]
	vpmadd52luq ymm15, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52huq ymm15, ymm23, YMMWORD PTR [r10+13088]
	vpmadd52luq ymm16, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52huq ymm16, ymm21, YMMWORD PTR [r8+13120]
	vpmadd52luq ymm16, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52huq ymm16, ymm23, YMMWORD PTR [r10+13120]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r8+13152]
	vpmadd52luq ymm17, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm17, ymm23, YMMWORD PTR [r10+13152]
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm18, ymm21, YMMWORD PTR [r8+13184]
	vpmadd52luq ymm18, ymm23, YMMWORD PTR [r10+13216]
	vpmadd52huq ymm18, ymm23, YMMWORD PTR [r10+13184]
	vpmadd52huq ymm9, ymm20, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm19, ymm21, YMMWORD PTR [r8+13216]
	vpmadd52huq ymm19, ymm23, YMMWORD PTR [r10+13216]
	add r9, 8
	sub rcx, 1
	jne 246b
	vmovdqu64 YMMWORD PTR [r11], ymm0
	vmovdqu64 YMMWORD PTR [r11+32], ymm1
	vmovdqu64 YMMWORD PTR [r11+64], ymm2
	vmovdqu64 YMMWORD PTR [r11+96], ymm3
	vmovdqu64 YMMWORD PTR [r11+128], ymm4
	vmovdqu64 YMMWORD PTR [r11+160], ymm5
	vmovdqu64 YMMWORD PTR [r11+192], ymm6
	vmovdqu64 YMMWORD PTR [r11+224], ymm7
	vmovdqu64 YMMWORD PTR [r11+256], ymm8
	vmovdqu64 YMMWORD PTR [r11+288], ymm9
	vmovdqu64 YMMWORD PTR [r11+12928], ymm10
	vmovdqu64 YMMWORD PTR [r11+12960], ymm11
	vmovdqu64 YMMWORD PTR [r11+12992], ymm12
	vmovdqu64 YMMWORD PTR [r11+13024], ymm13
	vmovdqu64 YMMWORD PTR [r11+13056], ymm14
	vmovdqu64 YMMWORD PTR [r11+13088], ymm15
	vmovdqu64 YMMWORD PTR [r11+13120], ymm16
	vmovdqu64 YMMWORD PTR [r11+13152], ymm17
	vmovdqu64 YMMWORD PTR [r11+13184], ymm18
	vmovdqu64 YMMWORD PTR [r11+13216], ymm19
	movabs r12, 4503599627370495
	mov edx, 0
	mov esi, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12928]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12928], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12960]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12960], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12992]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12992], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13024]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13024], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13056]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13056], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13088]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13088], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+192]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13120]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13120], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+224]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13152]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13152], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+256]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+256], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13184]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13184], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+288]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+288], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13216]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13216], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12936]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12936], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12968]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12968], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13000]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13000], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13032]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13032], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13064]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13064], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13096]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13096], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+200]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13128]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13128], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+232]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13160]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13160], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+264]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13192]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13192], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+296]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13224]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13224], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12944]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12944], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12976]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12976], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13008]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13008], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13040]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13040], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13072]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13072], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13104]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13104], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+208]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13136]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13136], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+240]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13168]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13168], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+272]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13200]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13200], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+304]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13232]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13232], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12952]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12952], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+12984]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+12984], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13016]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13016], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13048]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13048], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13080]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13080], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13112]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13112], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+216]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13144]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13144], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+248]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13176]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13176], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+280]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13208]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13208], rcx
	shr rsi, 52
	add rdx, QWORD PTR [r11+312]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+312], rax
	shr rdx, 52
	add rsi, QWORD PTR [r11+13240]
	mov rcx, rsi
	and rcx, r12
	mov QWORD PTR [r11+13240], rcx
	shr rsi, 52
	sub r15, 1
	jne 243b
	add r13, 1
	cmp r13, 417
	jne 238b
	vzeroupper
	mov r11, QWORD PTR [rdi+232]
	add r11, 13280
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
	mov rcx, QWORD PTR [r11+256]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+48], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+256]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+288]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+56], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+288]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+40]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+40]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+72]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+136]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+168]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+200]
	or rax, rcx
	mov rcx, QWORD PTR [r11+232]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+232]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+264]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+264]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+296]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+296]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+16]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+16]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+80]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+136], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+80]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+144], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+112]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+144]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+152], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+176]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+160], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+176]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+208]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+240]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+168], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+240]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+272]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+176], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+272]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+304]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+184], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+304]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+192], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+24]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+56]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+200], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+88]
	or rax, rcx
	mov rcx, QWORD PTR [r11+120]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+208], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+120]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+152]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+216], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+152]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+184]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+224], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+184]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+216]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+232], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+216]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+248]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+280]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+240], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+280]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+312]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+248], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+312]
	shr rcx, 20
	or rax, rcx
	mov QWORD PTR [r8+256], rax
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
	add r11, 352
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
	mov rcx, QWORD PTR [r11+256]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+48], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+256]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+288]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+56], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+288]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+8]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+40]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+64], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+40]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+72]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+72], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+72]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+104]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+80], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+104]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+136]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+88], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+136]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+168]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+96], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+200]
	or rax, rcx
	mov rcx, QWORD PTR [r11+232]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+104], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+232]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+264]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+112], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+264]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+296]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+120], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+296]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+16]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+128], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+16]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+48]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+80]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+136], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+80]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+112]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+144], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+112]
	shr rcx, 20
	or rax, rcx
	mov rcx, QWORD PTR [r11+144]
	ror rcx, 32
	movabs rbp, -4294967296
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+152], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+144]
	shr rcx, 32
	or rax, rcx
	mov rcx, QWORD PTR [r11+176]
	ror rcx, 44
	movabs rbp, -1048576
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+160], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+176]
	shr rcx, 44
	or rax, rcx
	mov rcx, QWORD PTR [r11+208]
	ror rcx, 56
	movabs rbp, -256
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+240]
	ror rcx, 4
	movabs rbp, -1152921504606846976
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+168], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+240]
	shr rcx, 4
	or rax, rcx
	mov rcx, QWORD PTR [r11+272]
	ror rcx, 16
	movabs rbp, -281474976710656
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+176], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+272]
	shr rcx, 16
	or rax, rcx
	mov rcx, QWORD PTR [r11+304]
	ror rcx, 28
	movabs rbp, -68719476736
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+184], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+304]
	shr rcx, 28
	or rax, rcx
	mov rcx, QWORD PTR [r11+24]
	ror rcx, 40
	movabs rbp, -16777216
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+192], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+24]
	shr rcx, 40
	or rax, rcx
	mov rcx, QWORD PTR [r11+56]
	ror rcx, 52
	movabs rbp, -4096
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+200], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+88]
	or rax, rcx
	mov rcx, QWORD PTR [r11+120]
	ror rcx, 12
	movabs rbp, -4503599627370496
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+208], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+120]
	shr rcx, 12
	or rax, rcx
	mov rcx, QWORD PTR [r11+152]
	ror rcx, 24
	movabs rbp, -1099511627776
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+216], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+152]
	shr rcx, 24
	or rax, rcx
	mov rcx, QWORD PTR [r11+184]
	ror rcx, 36
	movabs rbp, -268435456
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+224], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+184]
	shr rcx, 36
	or rax, rcx
	mov rcx, QWORD PTR [r11+216]
	ror rcx, 48
	movabs rbp, -65536
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+232], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+216]
	shr rcx, 48
	or rax, rcx
	mov rcx, QWORD PTR [r11+248]
	ror rcx, 60
	movabs rbp, -16
	and rcx, rbp
	or rax, rcx
	mov rcx, QWORD PTR [r11+280]
	ror rcx, 8
	movabs rbp, -72057594037927936
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+240], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+280]
	shr rcx, 8
	or rax, rcx
	mov rcx, QWORD PTR [r11+312]
	ror rcx, 20
	movabs rbp, -17592186044416
	and rcx, rbp
	or rax, rcx
	mov QWORD PTR [r8+248], rax
	mov eax, 0
	mov rcx, QWORD PTR [r11+312]
	shr rcx, 20
	or rax, rcx
	mov QWORD PTR [r8+256], rax
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
