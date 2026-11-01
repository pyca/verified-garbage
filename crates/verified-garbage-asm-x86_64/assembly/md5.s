// The functions of `src/md5.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_init:
	mov eax, 1732584193
	mov DWORD PTR [rdi], eax
	mov eax, -271733879
	mov DWORD PTR [rdi+4], eax
	mov eax, -1732584194
	mov DWORD PTR [rdi+8], eax
	mov eax, 271733878
	mov DWORD PTR [rdi+12], eax
	ret
	.p2align 6

vg_md5_update:
	lea rsp, [rsp-120]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+64], rbx
	mov QWORD PTR [r8+72], rbp
	mov QWORD PTR [r8+80], r12
	mov QWORD PTR [r8+88], r13
	mov QWORD PTR [r8+96], r14
	mov QWORD PTR [r8+104], r15
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
	mov QWORD PTR [rbx+r13*1+16], r9
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
	mov BYTE PTR [rbx+r13*1+16], r9b
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
	add rsi, 16
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
	mov QWORD PTR [rbx+r13*1+16], r9
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
	mov BYTE PTR [rbx+r13*1+16], r9b
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
	add rsi, 16
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
	call {vg_md5_compress}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+64]
	mov rbp, QWORD PTR [r15+72]
	mov r12, QWORD PTR [r15+80]
	mov r13, QWORD PTR [r15+88]
	mov r14, QWORD PTR [r15+96]
	mov r15, QWORD PTR [r15+104]
	lea rsp, [rsp+120]
	ret
	.p2align 6

vg_md5_finalize:
	lea rsp, [rsp-120]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+64], rbx
	mov QWORD PTR [rcx+72], rbp
	mov QWORD PTR [rcx+80], r12
	mov QWORD PTR [rcx+88], r13
	mov QWORD PTR [rcx+96], r14
	mov QWORD PTR [rcx+104], r15
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
	mov BYTE PTR [rbx+r13*1+16], r9b
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
	mov QWORD PTR [rbx+r13*1+16], r9
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
	mov BYTE PTR [rbx+r13*1+16], r9b
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
	mov QWORD PTR [rbx+72], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+16], xmm0
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
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+64], xmm0
24:
	mov rsi, rbx
	add rsi, 16
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_md5_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
	mov eax, DWORD PTR [rbx]
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	mov DWORD PTR [rbp+12], eax
	mov rbx, QWORD PTR [r15+64]
	mov rbp, QWORD PTR [r15+72]
	mov r12, QWORD PTR [r15+80]
	mov r13, QWORD PTR [r15+88]
	mov r14, QWORD PTR [r15+96]
	mov r15, QWORD PTR [r15+104]
	lea rsp, [rsp+120]
	ret
	.p2align 6
