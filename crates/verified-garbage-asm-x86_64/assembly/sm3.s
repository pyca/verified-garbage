// The functions of `src/sm3.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm3_init:
	mov eax, 1937774191
	mov DWORD PTR [rdi], eax
	mov eax, 1226093241
	mov DWORD PTR [rdi+4], eax
	mov eax, 388252375
	mov DWORD PTR [rdi+8], eax
	mov eax, -628488704
	mov DWORD PTR [rdi+12], eax
	mov eax, -1452330820
	mov DWORD PTR [rdi+16], eax
	mov eax, 372324522
	mov DWORD PTR [rdi+20], eax
	mov eax, -477237683
	mov DWORD PTR [rdi+24], eax
	mov eax, -1325724082
	mov DWORD PTR [rdi+28], eax
	ret
	.p2align 6

vg_sm3_update:
	lea rsp, [rsp-168]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+112], rbx
	mov QWORD PTR [r8+120], rbp
	mov QWORD PTR [r8+128], r12
	mov QWORD PTR [r8+136], r13
	mov QWORD PTR [r8+144], r14
	mov QWORD PTR [r8+152], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 63
20:
	test r13, r13
	je 21f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 23f
	jmp 24f
23:
	mov rax, r12
24:
	sub r12, rax
	cmp rax, 8
	jb 25f
27:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+32], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 27b
	jmp 26f
25:
26:
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 64
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 32
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 64
	jae 213f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 215f
	jmp 216f
215:
	mov rax, r12
216:
	sub r12, rax
	cmp rax, 8
	jb 217f
219:
	mov r9, QWORD PTR [rbp]
	mov QWORD PTR [rbx+r13*1+32], r9
	add rbp, 8
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 219b
	jmp 218f
217:
218:
	test rax, rax
	je 220f
222:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 64
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 32
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 63
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 6
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sm3_compress}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	lea rsp, [rsp+168]
	ret
	.p2align 6

vg_sm3_finalize:
	lea rsp, [rsp-168]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+112], rbx
	mov QWORD PTR [rcx+120], rbp
	mov QWORD PTR [rcx+128], r12
	mov QWORD PTR [rcx+136], r13
	mov QWORD PTR [rcx+144], r14
	mov QWORD PTR [rcx+152], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+32], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+32], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+80], xmm0
24:
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sm3_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
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
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	lea rsp, [rsp+168]
	ret
	.p2align 6
