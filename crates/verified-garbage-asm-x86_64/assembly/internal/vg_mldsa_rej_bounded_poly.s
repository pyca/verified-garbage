// The functions of `src/internal/vg_mldsa_rej_bounded_poly.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_rej_bounded_poly:
	cmp esi, 2
	je 20f
	mov QWORD PTR [rcx+2024], rbx
	mov QWORD PTR [rcx+2032], rbp
	mov QWORD PTR [rcx+2040], r12
	mov rbx, rcx
	mov rbp, rdx
	mov rcx, rdi
	mov r8d, 66
	mov eax, 0
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rax
	mov QWORD PTR [rbx+16], rax
	mov QWORD PTR [rbx+24], rax
	mov QWORD PTR [rbx+32], rax
	mov QWORD PTR [rbx+40], rax
	mov QWORD PTR [rbx+48], rax
	mov QWORD PTR [rbx+56], rax
	mov QWORD PTR [rbx+64], rax
	mov QWORD PTR [rbx+72], rax
	mov QWORD PTR [rbx+80], rax
	mov QWORD PTR [rbx+88], rax
	mov QWORD PTR [rbx+96], rax
	mov QWORD PTR [rbx+104], rax
	mov QWORD PTR [rbx+112], rax
	mov QWORD PTR [rbx+120], rax
	mov QWORD PTR [rbx+128], rax
	mov QWORD PTR [rbx+136], rax
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rax
	mov QWORD PTR [rbx+160], rax
	mov QWORD PTR [rbx+168], rax
	mov QWORD PTR [rbx+176], rax
	mov QWORD PTR [rbx+184], rax
	mov QWORD PTR [rbx+192], rax
	mov rdi, rbx
	mov esi, 136
	mov edx, 0
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	mov esi, 136
	mov edx, 0
	mov rcx, rbx
	add rcx, 840
	mov r8d, 272
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov r12, rax
	mov rsi, rbx
	add rsi, 840
	mov edi, 0
	mov ecx, 272
22:
	movzx eax, BYTE PTR [rsi]
	mov edx, eax
	and edx, 15
	cmp rdi, 256
	jb 23f
	jmp 24f
23:
	cmp edx, 9
	jb 25f
	jmp 26f
25:
	mov r8d, 4
	sub r8d, edx
	sbb edx, edx
	and edx, 8380417
	add r8d, edx
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
26:
	shr eax, 4
	mov edx, eax
	cmp rdi, 256
	jb 27f
	jmp 28f
27:
	cmp edx, 9
	jb 29f
	jmp 210f
29:
	mov r8d, 4
	sub r8d, edx
	sbb edx, edx
	and edx, 8380417
	add r8d, edx
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
210:
28:
24:
	add rsi, 1
	sub rcx, 1
	jne 22b
	cmp rdi, 256
	je 211f
	mov QWORD PTR [rbx+2016], rdi
	mov rdi, rbx
	mov esi, 136
	mov rdx, r12
	mov rcx, rbx
	add rcx, 1112
	mov r8d, 272
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rbx+2016]
	mov rsi, rbx
	add rsi, 1112
	mov ecx, 272
	mov r12d, 4
213:
	movzx eax, BYTE PTR [rsi]
	mov edx, eax
	and edx, 15
	cmp rdi, 256
	jb 214f
	jmp 215f
214:
	cmp edx, 9
	jb 216f
	jmp 217f
216:
	mov r8d, 4
	sub r8d, edx
	sbb edx, edx
	and edx, 8380417
	add r8d, edx
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
217:
	shr eax, 4
	mov edx, eax
	cmp rdi, 256
	jb 218f
	jmp 219f
218:
	cmp edx, 9
	jb 220f
	jmp 221f
220:
	mov r8d, 4
	sub r8d, edx
	sbb edx, edx
	and edx, 8380417
	add r8d, edx
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
221:
219:
215:
	add rsi, 1
	sub rcx, 1
	jne 213b
	mov rax, rdi
	shr rax, 8
	mov rbp, QWORD PTR [rbx+2032]
	mov r12, QWORD PTR [rbx+2040]
	mov rbx, QWORD PTR [rbx+2024]
	jmp 212f
211:
	mov rax, rdi
	shr rax, 8
	mov rbp, QWORD PTR [rbx+2032]
	mov r12, QWORD PTR [rbx+2040]
	mov rbx, QWORD PTR [rbx+2024]
212:
	jmp 21f
20:
	mov QWORD PTR [rcx+2024], rbx
	mov QWORD PTR [rcx+2032], rbp
	mov QWORD PTR [rcx+2040], r12
	mov rbx, rcx
	mov rbp, rdx
	mov rcx, rdi
	mov r8d, 66
	mov eax, 0
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rax
	mov QWORD PTR [rbx+16], rax
	mov QWORD PTR [rbx+24], rax
	mov QWORD PTR [rbx+32], rax
	mov QWORD PTR [rbx+40], rax
	mov QWORD PTR [rbx+48], rax
	mov QWORD PTR [rbx+56], rax
	mov QWORD PTR [rbx+64], rax
	mov QWORD PTR [rbx+72], rax
	mov QWORD PTR [rbx+80], rax
	mov QWORD PTR [rbx+88], rax
	mov QWORD PTR [rbx+96], rax
	mov QWORD PTR [rbx+104], rax
	mov QWORD PTR [rbx+112], rax
	mov QWORD PTR [rbx+120], rax
	mov QWORD PTR [rbx+128], rax
	mov QWORD PTR [rbx+136], rax
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rax
	mov QWORD PTR [rbx+160], rax
	mov QWORD PTR [rbx+168], rax
	mov QWORD PTR [rbx+176], rax
	mov QWORD PTR [rbx+184], rax
	mov QWORD PTR [rbx+192], rax
	mov rdi, rbx
	mov esi, 136
	mov edx, 0
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	mov esi, 136
	mov edx, 0
	mov rcx, rbx
	add rcx, 840
	mov r8d, 272
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov r12, rax
	mov rsi, rbx
	add rsi, 840
	mov edi, 0
	mov ecx, 272
222:
	movzx eax, BYTE PTR [rsi]
	mov edx, eax
	and edx, 15
	cmp rdi, 256
	jb 223f
	jmp 224f
223:
	cmp edx, 15
	jb 225f
	jmp 226f
225:
	sub edx, 10
	sbb r8d, r8d
	and r8d, 10
	add edx, r8d
	sub edx, 5
	sbb r8d, r8d
	and r8d, 5
	add edx, r8d
	mov r8d, 2
	sub r8d, edx
	sbb edx, edx
	and edx, 8380417
	add r8d, edx
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
226:
	shr eax, 4
	mov edx, eax
	cmp rdi, 256
	jb 227f
	jmp 228f
227:
	cmp edx, 15
	jb 229f
	jmp 230f
229:
	sub edx, 10
	sbb r8d, r8d
	and r8d, 10
	add edx, r8d
	sub edx, 5
	sbb r8d, r8d
	and r8d, 5
	add edx, r8d
	mov r8d, 2
	sub r8d, edx
	sbb edx, edx
	and edx, 8380417
	add r8d, edx
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
230:
228:
224:
	add rsi, 1
	sub rcx, 1
	jne 222b
	cmp rdi, 256
	je 231f
	mov QWORD PTR [rbx+2016], rdi
	mov rdi, rbx
	mov esi, 136
	mov rdx, r12
	mov rcx, rbx
	add rcx, 1112
	mov r8d, 272
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rdi, QWORD PTR [rbx+2016]
	mov rsi, rbx
	add rsi, 1112
	mov ecx, 272
	mov r12d, 2
233:
	movzx eax, BYTE PTR [rsi]
	mov edx, eax
	and edx, 15
	cmp rdi, 256
	jb 234f
	jmp 235f
234:
	cmp edx, 15
	jb 236f
	jmp 237f
236:
	sub edx, 10
	sbb r8d, r8d
	and r8d, 10
	add edx, r8d
	sub edx, 5
	sbb r8d, r8d
	and r8d, 5
	add edx, r8d
	mov r8d, 2
	sub r8d, edx
	sbb edx, edx
	and edx, 8380417
	add r8d, edx
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
237:
	shr eax, 4
	mov edx, eax
	cmp rdi, 256
	jb 238f
	jmp 239f
238:
	cmp edx, 15
	jb 240f
	jmp 241f
240:
	sub edx, 10
	sbb r8d, r8d
	and r8d, 10
	add edx, r8d
	sub edx, 5
	sbb r8d, r8d
	and r8d, 5
	add edx, r8d
	mov r8d, 2
	sub r8d, edx
	sbb edx, edx
	and edx, 8380417
	add r8d, edx
	mov DWORD PTR [rbp+rdi*4], r8d
	add rdi, 1
241:
239:
235:
	add rsi, 1
	sub rcx, 1
	jne 233b
	mov rax, rdi
	shr rax, 8
	mov rbp, QWORD PTR [rbx+2032]
	mov r12, QWORD PTR [rbx+2040]
	mov rbx, QWORD PTR [rbx+2024]
	jmp 232f
231:
	mov rax, rdi
	shr rax, 8
	mov rbp, QWORD PTR [rbx+2032]
	mov r12, QWORD PTR [rbx+2040]
	mov rbx, QWORD PTR [rbx+2024]
232:
21:
	ret
	.p2align 6
