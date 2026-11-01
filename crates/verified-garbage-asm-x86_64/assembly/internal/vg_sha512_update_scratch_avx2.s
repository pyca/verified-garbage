// The functions of `src/internal/vg_sha512_update_scratch_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_update_scratch_avx2:
	mov QWORD PTR [r8+1328], rbx
	mov QWORD PTR [r8+1336], rbp
	mov QWORD PTR [r8+1344], r12
	mov QWORD PTR [r8+1352], r13
	mov QWORD PTR [r8+1360], r14
	mov QWORD PTR [r8+1368], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r13, rsi
	and r13, 127
20:
	test r13, r13
	je 21f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	mov r14d, 0
	cmp r13, 128
	je 211f
	jmp 212f
211:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
212:
	jmp 22f
21:
	cmp r12, 128
	jae 213f
	mov eax, 128
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
	mov QWORD PTR [rbx+r13*1+64], r9
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
	mov BYTE PTR [rbx+r13*1+64], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 222b
	jmp 221f
220:
221:
	mov r14d, 0
	cmp r13, 128
	je 223f
	jmp 224f
223:
	mov rsi, rbx
	add rsi, 64
	mov r13d, 0
	mov r14d, 1
224:
	jmp 214f
213:
	mov rsi, rbp
	mov rax, r12
	and rax, 127
	mov r14, r12
	sub r14, rax
	add rbp, r14
	mov r12, rax
	shr r14, 7
214:
22:
	test r14, r14
	jne 225f
	jmp 226f
225:
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
226:
	test r14, r14
	jne 20b
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	ret
	.p2align 6
