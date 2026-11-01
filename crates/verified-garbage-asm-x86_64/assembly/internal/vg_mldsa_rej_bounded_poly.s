// The functions of `src/internal/vg_mldsa_rej_bounded_poly.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_rej_bounded_poly:
	mov QWORD PTR [rcx+2024], rbx
	mov QWORD PTR [rcx+2032], rbp
	mov QWORD PTR [rcx+2040], r12
	mov rbx, rcx
	mov rbp, rdx
	mov r12d, esi
	mov rcx, rdi
	mov r8, 66
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
	mov r8d, 544
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	cmp r12d, 2
	je 20f
	mov rsi, rbx
	add rsi, 840
	mov edi, 0
	mov ecx, 544
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
	jmp 21f
20:
	mov rsi, rbx
	add rsi, 840
	mov edi, 0
	mov ecx, 544
211:
	movzx eax, BYTE PTR [rsi]
	mov edx, eax
	and edx, 15
	cmp rdi, 256
	jb 212f
	jmp 213f
212:
	cmp edx, 15
	jb 214f
	jmp 215f
214:
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
215:
	shr eax, 4
	mov edx, eax
	cmp rdi, 256
	jb 216f
	jmp 217f
216:
	cmp edx, 15
	jb 218f
	jmp 219f
218:
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
219:
217:
213:
	add rsi, 1
	sub rcx, 1
	jne 211b
21:
	mov rax, rdi
	shr rax, 8
	mov rbp, QWORD PTR [rbx+2032]
	mov r12, QWORD PTR [rbx+2040]
	mov rbx, QWORD PTR [rbx+2024]
	ret
	.p2align 6
