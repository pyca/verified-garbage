// The functions of `src/scrypt.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_blockmix:
	mov QWORD PTR [r8+64], rbx
	mov QWORD PTR [r8+72], rbp
	mov QWORD PTR [r8+80], r12
	mov QWORD PTR [r8+88], r14
	mov QWORD PTR [r8+96], r15
	mov QWORD PTR [r8+104], r13
	mov r14, rsi
	mov rbx, rdi
	mov rbp, rdx
	mov r13, r8
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	mov r12, rdx
	add r12, rsi
	mov r15, rdi
	add r15, rsi
	add r15, rsi
	sub r15, 64
	mov QWORD PTR [r13+16], rbx
	mov QWORD PTR [r13+24], rbp
	mov QWORD PTR [r13+32], r12
	mov QWORD PTR [r13+40], r14
	mov rsi, r13
	mov rdi, r15
	mov ecx, DWORD PTR [rdi]
	mov edx, DWORD PTR [rdi+4]
	mov r8d, DWORD PTR [rdi+8]
	mov r9d, DWORD PTR [rdi+12]
	mov r10d, DWORD PTR [rdi+16]
	mov r11d, DWORD PTR [rdi+20]
	mov ebx, DWORD PTR [rdi+24]
	mov ebp, DWORD PTR [rdi+28]
	mov r12d, DWORD PTR [rdi+32]
	mov r13d, DWORD PTR [rdi+36]
	mov r14d, DWORD PTR [rdi+40]
	mov r15d, DWORD PTR [rdi+44]
	mov eax, DWORD PTR [rdi+48]
	mov DWORD PTR [rsi], eax
	mov eax, DWORD PTR [rdi+52]
	mov DWORD PTR [rsi+4], eax
	mov eax, DWORD PTR [rdi+56]
	mov DWORD PTR [rsi+8], eax
	mov eax, DWORD PTR [rdi+60]
	mov DWORD PTR [rsi+12], eax
20:
	mov rax, QWORD PTR [rsi+16]
	add rax, 0
	mov rdi, QWORD PTR [rsi+24]
	xor ecx, DWORD PTR [rax]
	mov DWORD PTR [rdi], ecx
	xor edx, DWORD PTR [rax+4]
	mov DWORD PTR [rdi+4], edx
	xor r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi+8], r8d
	xor r9d, DWORD PTR [rax+12]
	mov DWORD PTR [rdi+12], r9d
	xor r10d, DWORD PTR [rax+16]
	mov DWORD PTR [rdi+16], r10d
	xor r11d, DWORD PTR [rax+20]
	mov DWORD PTR [rdi+20], r11d
	xor ebx, DWORD PTR [rax+24]
	mov DWORD PTR [rdi+24], ebx
	xor ebp, DWORD PTR [rax+28]
	mov DWORD PTR [rdi+28], ebp
	xor r12d, DWORD PTR [rax+32]
	mov DWORD PTR [rdi+32], r12d
	xor r13d, DWORD PTR [rax+36]
	mov DWORD PTR [rdi+36], r13d
	xor r14d, DWORD PTR [rax+40]
	mov DWORD PTR [rdi+40], r14d
	xor r15d, DWORD PTR [rax+44]
	mov DWORD PTR [rdi+44], r15d
	mov QWORD PTR [rsi+48], rcx
	mov ecx, DWORD PTR [rsi]
	xor ecx, DWORD PTR [rax+48]
	mov DWORD PTR [rdi+48], ecx
	mov DWORD PTR [rsi], ecx
	mov ecx, DWORD PTR [rsi+4]
	xor ecx, DWORD PTR [rax+52]
	mov DWORD PTR [rdi+52], ecx
	mov DWORD PTR [rsi+4], ecx
	mov ecx, DWORD PTR [rsi+8]
	xor ecx, DWORD PTR [rax+56]
	mov DWORD PTR [rdi+56], ecx
	mov DWORD PTR [rsi+8], ecx
	mov ecx, DWORD PTR [rsi+12]
	xor ecx, DWORD PTR [rax+60]
	mov DWORD PTR [rdi+60], ecx
	mov DWORD PTR [rsi+12], ecx
	mov rcx, QWORD PTR [rsi+48]
	mov eax, ecx
	add eax, DWORD PTR [rsi]
	ror eax, 25
	xor r10d, eax
	mov eax, r11d
	add eax, edx
	ror eax, 25
	xor r13d, eax
	mov eax, r14d
	add eax, ebx
	ror eax, 25
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, DWORD PTR [rsi+12]
	add eax, r15d
	ror eax, 25
	xor r9d, eax
	mov eax, r10d
	add eax, ecx
	ror eax, 23
	xor r12d, eax
	mov eax, r13d
	add eax, r11d
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, DWORD PTR [rsi+8]
	add eax, r14d
	ror eax, 23
	xor r8d, eax
	mov eax, r9d
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor ebp, eax
	mov eax, r12d
	add eax, r10d
	ror eax, 19
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, DWORD PTR [rsi+4]
	add eax, r13d
	ror eax, 19
	xor edx, eax
	mov eax, r8d
	add eax, DWORD PTR [rsi+8]
	ror eax, 19
	xor ebx, eax
	mov eax, ebp
	add eax, r9d
	ror eax, 19
	xor r15d, eax
	mov eax, DWORD PTR [rsi]
	add eax, r12d
	ror eax, 14
	xor ecx, eax
	mov eax, edx
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor r11d, eax
	mov eax, ebx
	add eax, r8d
	ror eax, 14
	xor r14d, eax
	mov eax, r15d
	add eax, ebp
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	mov eax, ecx
	add eax, r9d
	ror eax, 25
	xor edx, eax
	mov eax, r11d
	add eax, r10d
	ror eax, 25
	xor ebx, eax
	mov eax, r14d
	add eax, r13d
	ror eax, 25
	xor r15d, eax
	mov eax, DWORD PTR [rsi+12]
	add eax, DWORD PTR [rsi+8]
	ror eax, 25
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, edx
	add eax, ecx
	ror eax, 23
	xor r8d, eax
	mov eax, ebx
	add eax, r11d
	ror eax, 23
	xor ebp, eax
	mov eax, r15d
	add eax, r14d
	ror eax, 23
	xor r12d, eax
	mov eax, DWORD PTR [rsi]
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, r8d
	add eax, edx
	ror eax, 19
	xor r9d, eax
	mov eax, ebp
	add eax, ebx
	ror eax, 19
	xor r10d, eax
	mov eax, r12d
	add eax, r15d
	ror eax, 19
	xor r13d, eax
	mov eax, DWORD PTR [rsi+4]
	add eax, DWORD PTR [rsi]
	ror eax, 19
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, r9d
	add eax, r8d
	ror eax, 14
	xor ecx, eax
	mov eax, r10d
	add eax, ebp
	ror eax, 14
	xor r11d, eax
	mov eax, r13d
	add eax, r12d
	ror eax, 14
	xor r14d, eax
	mov eax, DWORD PTR [rsi+8]
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	mov eax, ecx
	add eax, DWORD PTR [rsi]
	ror eax, 25
	xor r10d, eax
	mov eax, r11d
	add eax, edx
	ror eax, 25
	xor r13d, eax
	mov eax, r14d
	add eax, ebx
	ror eax, 25
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, DWORD PTR [rsi+12]
	add eax, r15d
	ror eax, 25
	xor r9d, eax
	mov eax, r10d
	add eax, ecx
	ror eax, 23
	xor r12d, eax
	mov eax, r13d
	add eax, r11d
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, DWORD PTR [rsi+8]
	add eax, r14d
	ror eax, 23
	xor r8d, eax
	mov eax, r9d
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor ebp, eax
	mov eax, r12d
	add eax, r10d
	ror eax, 19
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, DWORD PTR [rsi+4]
	add eax, r13d
	ror eax, 19
	xor edx, eax
	mov eax, r8d
	add eax, DWORD PTR [rsi+8]
	ror eax, 19
	xor ebx, eax
	mov eax, ebp
	add eax, r9d
	ror eax, 19
	xor r15d, eax
	mov eax, DWORD PTR [rsi]
	add eax, r12d
	ror eax, 14
	xor ecx, eax
	mov eax, edx
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor r11d, eax
	mov eax, ebx
	add eax, r8d
	ror eax, 14
	xor r14d, eax
	mov eax, r15d
	add eax, ebp
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	mov eax, ecx
	add eax, r9d
	ror eax, 25
	xor edx, eax
	mov eax, r11d
	add eax, r10d
	ror eax, 25
	xor ebx, eax
	mov eax, r14d
	add eax, r13d
	ror eax, 25
	xor r15d, eax
	mov eax, DWORD PTR [rsi+12]
	add eax, DWORD PTR [rsi+8]
	ror eax, 25
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, edx
	add eax, ecx
	ror eax, 23
	xor r8d, eax
	mov eax, ebx
	add eax, r11d
	ror eax, 23
	xor ebp, eax
	mov eax, r15d
	add eax, r14d
	ror eax, 23
	xor r12d, eax
	mov eax, DWORD PTR [rsi]
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, r8d
	add eax, edx
	ror eax, 19
	xor r9d, eax
	mov eax, ebp
	add eax, ebx
	ror eax, 19
	xor r10d, eax
	mov eax, r12d
	add eax, r15d
	ror eax, 19
	xor r13d, eax
	mov eax, DWORD PTR [rsi+4]
	add eax, DWORD PTR [rsi]
	ror eax, 19
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, r9d
	add eax, r8d
	ror eax, 14
	xor ecx, eax
	mov eax, r10d
	add eax, ebp
	ror eax, 14
	xor r11d, eax
	mov eax, r13d
	add eax, r12d
	ror eax, 14
	xor r14d, eax
	mov eax, DWORD PTR [rsi+8]
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	mov eax, ecx
	add eax, DWORD PTR [rsi]
	ror eax, 25
	xor r10d, eax
	mov eax, r11d
	add eax, edx
	ror eax, 25
	xor r13d, eax
	mov eax, r14d
	add eax, ebx
	ror eax, 25
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, DWORD PTR [rsi+12]
	add eax, r15d
	ror eax, 25
	xor r9d, eax
	mov eax, r10d
	add eax, ecx
	ror eax, 23
	xor r12d, eax
	mov eax, r13d
	add eax, r11d
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, DWORD PTR [rsi+8]
	add eax, r14d
	ror eax, 23
	xor r8d, eax
	mov eax, r9d
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor ebp, eax
	mov eax, r12d
	add eax, r10d
	ror eax, 19
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, DWORD PTR [rsi+4]
	add eax, r13d
	ror eax, 19
	xor edx, eax
	mov eax, r8d
	add eax, DWORD PTR [rsi+8]
	ror eax, 19
	xor ebx, eax
	mov eax, ebp
	add eax, r9d
	ror eax, 19
	xor r15d, eax
	mov eax, DWORD PTR [rsi]
	add eax, r12d
	ror eax, 14
	xor ecx, eax
	mov eax, edx
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor r11d, eax
	mov eax, ebx
	add eax, r8d
	ror eax, 14
	xor r14d, eax
	mov eax, r15d
	add eax, ebp
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	mov eax, ecx
	add eax, r9d
	ror eax, 25
	xor edx, eax
	mov eax, r11d
	add eax, r10d
	ror eax, 25
	xor ebx, eax
	mov eax, r14d
	add eax, r13d
	ror eax, 25
	xor r15d, eax
	mov eax, DWORD PTR [rsi+12]
	add eax, DWORD PTR [rsi+8]
	ror eax, 25
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, edx
	add eax, ecx
	ror eax, 23
	xor r8d, eax
	mov eax, ebx
	add eax, r11d
	ror eax, 23
	xor ebp, eax
	mov eax, r15d
	add eax, r14d
	ror eax, 23
	xor r12d, eax
	mov eax, DWORD PTR [rsi]
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, r8d
	add eax, edx
	ror eax, 19
	xor r9d, eax
	mov eax, ebp
	add eax, ebx
	ror eax, 19
	xor r10d, eax
	mov eax, r12d
	add eax, r15d
	ror eax, 19
	xor r13d, eax
	mov eax, DWORD PTR [rsi+4]
	add eax, DWORD PTR [rsi]
	ror eax, 19
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, r9d
	add eax, r8d
	ror eax, 14
	xor ecx, eax
	mov eax, r10d
	add eax, ebp
	ror eax, 14
	xor r11d, eax
	mov eax, r13d
	add eax, r12d
	ror eax, 14
	xor r14d, eax
	mov eax, DWORD PTR [rsi+8]
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	mov eax, ecx
	add eax, DWORD PTR [rsi]
	ror eax, 25
	xor r10d, eax
	mov eax, r11d
	add eax, edx
	ror eax, 25
	xor r13d, eax
	mov eax, r14d
	add eax, ebx
	ror eax, 25
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, DWORD PTR [rsi+12]
	add eax, r15d
	ror eax, 25
	xor r9d, eax
	mov eax, r10d
	add eax, ecx
	ror eax, 23
	xor r12d, eax
	mov eax, r13d
	add eax, r11d
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, DWORD PTR [rsi+8]
	add eax, r14d
	ror eax, 23
	xor r8d, eax
	mov eax, r9d
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor ebp, eax
	mov eax, r12d
	add eax, r10d
	ror eax, 19
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, DWORD PTR [rsi+4]
	add eax, r13d
	ror eax, 19
	xor edx, eax
	mov eax, r8d
	add eax, DWORD PTR [rsi+8]
	ror eax, 19
	xor ebx, eax
	mov eax, ebp
	add eax, r9d
	ror eax, 19
	xor r15d, eax
	mov eax, DWORD PTR [rsi]
	add eax, r12d
	ror eax, 14
	xor ecx, eax
	mov eax, edx
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor r11d, eax
	mov eax, ebx
	add eax, r8d
	ror eax, 14
	xor r14d, eax
	mov eax, r15d
	add eax, ebp
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	mov eax, ecx
	add eax, r9d
	ror eax, 25
	xor edx, eax
	mov eax, r11d
	add eax, r10d
	ror eax, 25
	xor ebx, eax
	mov eax, r14d
	add eax, r13d
	ror eax, 25
	xor r15d, eax
	mov eax, DWORD PTR [rsi+12]
	add eax, DWORD PTR [rsi+8]
	ror eax, 25
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, edx
	add eax, ecx
	ror eax, 23
	xor r8d, eax
	mov eax, ebx
	add eax, r11d
	ror eax, 23
	xor ebp, eax
	mov eax, r15d
	add eax, r14d
	ror eax, 23
	xor r12d, eax
	mov eax, DWORD PTR [rsi]
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, r8d
	add eax, edx
	ror eax, 19
	xor r9d, eax
	mov eax, ebp
	add eax, ebx
	ror eax, 19
	xor r10d, eax
	mov eax, r12d
	add eax, r15d
	ror eax, 19
	xor r13d, eax
	mov eax, DWORD PTR [rsi+4]
	add eax, DWORD PTR [rsi]
	ror eax, 19
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, r9d
	add eax, r8d
	ror eax, 14
	xor ecx, eax
	mov eax, r10d
	add eax, ebp
	ror eax, 14
	xor r11d, eax
	mov eax, r13d
	add eax, r12d
	ror eax, 14
	xor r14d, eax
	mov eax, DWORD PTR [rsi+8]
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	add ecx, DWORD PTR [rdi]
	mov DWORD PTR [rdi], ecx
	add edx, DWORD PTR [rdi+4]
	mov DWORD PTR [rdi+4], edx
	add r8d, DWORD PTR [rdi+8]
	mov DWORD PTR [rdi+8], r8d
	add r9d, DWORD PTR [rdi+12]
	mov DWORD PTR [rdi+12], r9d
	add r10d, DWORD PTR [rdi+16]
	mov DWORD PTR [rdi+16], r10d
	add r11d, DWORD PTR [rdi+20]
	mov DWORD PTR [rdi+20], r11d
	add ebx, DWORD PTR [rdi+24]
	mov DWORD PTR [rdi+24], ebx
	add ebp, DWORD PTR [rdi+28]
	mov DWORD PTR [rdi+28], ebp
	add r12d, DWORD PTR [rdi+32]
	mov DWORD PTR [rdi+32], r12d
	add r13d, DWORD PTR [rdi+36]
	mov DWORD PTR [rdi+36], r13d
	add r14d, DWORD PTR [rdi+40]
	mov DWORD PTR [rdi+40], r14d
	add r15d, DWORD PTR [rdi+44]
	mov DWORD PTR [rdi+44], r15d
	mov eax, DWORD PTR [rsi]
	add eax, DWORD PTR [rdi+48]
	mov DWORD PTR [rdi+48], eax
	mov DWORD PTR [rsi], eax
	mov eax, DWORD PTR [rsi+4]
	add eax, DWORD PTR [rdi+52]
	mov DWORD PTR [rdi+52], eax
	mov DWORD PTR [rsi+4], eax
	mov eax, DWORD PTR [rsi+8]
	add eax, DWORD PTR [rdi+56]
	mov DWORD PTR [rdi+56], eax
	mov DWORD PTR [rsi+8], eax
	mov eax, DWORD PTR [rsi+12]
	add eax, DWORD PTR [rdi+60]
	mov DWORD PTR [rdi+60], eax
	mov DWORD PTR [rsi+12], eax
	mov rax, QWORD PTR [rsi+16]
	add rax, 64
	mov rdi, QWORD PTR [rsi+32]
	xor ecx, DWORD PTR [rax]
	mov DWORD PTR [rdi], ecx
	xor edx, DWORD PTR [rax+4]
	mov DWORD PTR [rdi+4], edx
	xor r8d, DWORD PTR [rax+8]
	mov DWORD PTR [rdi+8], r8d
	xor r9d, DWORD PTR [rax+12]
	mov DWORD PTR [rdi+12], r9d
	xor r10d, DWORD PTR [rax+16]
	mov DWORD PTR [rdi+16], r10d
	xor r11d, DWORD PTR [rax+20]
	mov DWORD PTR [rdi+20], r11d
	xor ebx, DWORD PTR [rax+24]
	mov DWORD PTR [rdi+24], ebx
	xor ebp, DWORD PTR [rax+28]
	mov DWORD PTR [rdi+28], ebp
	xor r12d, DWORD PTR [rax+32]
	mov DWORD PTR [rdi+32], r12d
	xor r13d, DWORD PTR [rax+36]
	mov DWORD PTR [rdi+36], r13d
	xor r14d, DWORD PTR [rax+40]
	mov DWORD PTR [rdi+40], r14d
	xor r15d, DWORD PTR [rax+44]
	mov DWORD PTR [rdi+44], r15d
	mov QWORD PTR [rsi+48], rcx
	mov ecx, DWORD PTR [rsi]
	xor ecx, DWORD PTR [rax+48]
	mov DWORD PTR [rdi+48], ecx
	mov DWORD PTR [rsi], ecx
	mov ecx, DWORD PTR [rsi+4]
	xor ecx, DWORD PTR [rax+52]
	mov DWORD PTR [rdi+52], ecx
	mov DWORD PTR [rsi+4], ecx
	mov ecx, DWORD PTR [rsi+8]
	xor ecx, DWORD PTR [rax+56]
	mov DWORD PTR [rdi+56], ecx
	mov DWORD PTR [rsi+8], ecx
	mov ecx, DWORD PTR [rsi+12]
	xor ecx, DWORD PTR [rax+60]
	mov DWORD PTR [rdi+60], ecx
	mov DWORD PTR [rsi+12], ecx
	mov rcx, QWORD PTR [rsi+48]
	mov eax, ecx
	add eax, DWORD PTR [rsi]
	ror eax, 25
	xor r10d, eax
	mov eax, r11d
	add eax, edx
	ror eax, 25
	xor r13d, eax
	mov eax, r14d
	add eax, ebx
	ror eax, 25
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, DWORD PTR [rsi+12]
	add eax, r15d
	ror eax, 25
	xor r9d, eax
	mov eax, r10d
	add eax, ecx
	ror eax, 23
	xor r12d, eax
	mov eax, r13d
	add eax, r11d
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, DWORD PTR [rsi+8]
	add eax, r14d
	ror eax, 23
	xor r8d, eax
	mov eax, r9d
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor ebp, eax
	mov eax, r12d
	add eax, r10d
	ror eax, 19
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, DWORD PTR [rsi+4]
	add eax, r13d
	ror eax, 19
	xor edx, eax
	mov eax, r8d
	add eax, DWORD PTR [rsi+8]
	ror eax, 19
	xor ebx, eax
	mov eax, ebp
	add eax, r9d
	ror eax, 19
	xor r15d, eax
	mov eax, DWORD PTR [rsi]
	add eax, r12d
	ror eax, 14
	xor ecx, eax
	mov eax, edx
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor r11d, eax
	mov eax, ebx
	add eax, r8d
	ror eax, 14
	xor r14d, eax
	mov eax, r15d
	add eax, ebp
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	mov eax, ecx
	add eax, r9d
	ror eax, 25
	xor edx, eax
	mov eax, r11d
	add eax, r10d
	ror eax, 25
	xor ebx, eax
	mov eax, r14d
	add eax, r13d
	ror eax, 25
	xor r15d, eax
	mov eax, DWORD PTR [rsi+12]
	add eax, DWORD PTR [rsi+8]
	ror eax, 25
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, edx
	add eax, ecx
	ror eax, 23
	xor r8d, eax
	mov eax, ebx
	add eax, r11d
	ror eax, 23
	xor ebp, eax
	mov eax, r15d
	add eax, r14d
	ror eax, 23
	xor r12d, eax
	mov eax, DWORD PTR [rsi]
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, r8d
	add eax, edx
	ror eax, 19
	xor r9d, eax
	mov eax, ebp
	add eax, ebx
	ror eax, 19
	xor r10d, eax
	mov eax, r12d
	add eax, r15d
	ror eax, 19
	xor r13d, eax
	mov eax, DWORD PTR [rsi+4]
	add eax, DWORD PTR [rsi]
	ror eax, 19
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, r9d
	add eax, r8d
	ror eax, 14
	xor ecx, eax
	mov eax, r10d
	add eax, ebp
	ror eax, 14
	xor r11d, eax
	mov eax, r13d
	add eax, r12d
	ror eax, 14
	xor r14d, eax
	mov eax, DWORD PTR [rsi+8]
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	mov eax, ecx
	add eax, DWORD PTR [rsi]
	ror eax, 25
	xor r10d, eax
	mov eax, r11d
	add eax, edx
	ror eax, 25
	xor r13d, eax
	mov eax, r14d
	add eax, ebx
	ror eax, 25
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, DWORD PTR [rsi+12]
	add eax, r15d
	ror eax, 25
	xor r9d, eax
	mov eax, r10d
	add eax, ecx
	ror eax, 23
	xor r12d, eax
	mov eax, r13d
	add eax, r11d
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, DWORD PTR [rsi+8]
	add eax, r14d
	ror eax, 23
	xor r8d, eax
	mov eax, r9d
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor ebp, eax
	mov eax, r12d
	add eax, r10d
	ror eax, 19
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, DWORD PTR [rsi+4]
	add eax, r13d
	ror eax, 19
	xor edx, eax
	mov eax, r8d
	add eax, DWORD PTR [rsi+8]
	ror eax, 19
	xor ebx, eax
	mov eax, ebp
	add eax, r9d
	ror eax, 19
	xor r15d, eax
	mov eax, DWORD PTR [rsi]
	add eax, r12d
	ror eax, 14
	xor ecx, eax
	mov eax, edx
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor r11d, eax
	mov eax, ebx
	add eax, r8d
	ror eax, 14
	xor r14d, eax
	mov eax, r15d
	add eax, ebp
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	mov eax, ecx
	add eax, r9d
	ror eax, 25
	xor edx, eax
	mov eax, r11d
	add eax, r10d
	ror eax, 25
	xor ebx, eax
	mov eax, r14d
	add eax, r13d
	ror eax, 25
	xor r15d, eax
	mov eax, DWORD PTR [rsi+12]
	add eax, DWORD PTR [rsi+8]
	ror eax, 25
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, edx
	add eax, ecx
	ror eax, 23
	xor r8d, eax
	mov eax, ebx
	add eax, r11d
	ror eax, 23
	xor ebp, eax
	mov eax, r15d
	add eax, r14d
	ror eax, 23
	xor r12d, eax
	mov eax, DWORD PTR [rsi]
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, r8d
	add eax, edx
	ror eax, 19
	xor r9d, eax
	mov eax, ebp
	add eax, ebx
	ror eax, 19
	xor r10d, eax
	mov eax, r12d
	add eax, r15d
	ror eax, 19
	xor r13d, eax
	mov eax, DWORD PTR [rsi+4]
	add eax, DWORD PTR [rsi]
	ror eax, 19
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, r9d
	add eax, r8d
	ror eax, 14
	xor ecx, eax
	mov eax, r10d
	add eax, ebp
	ror eax, 14
	xor r11d, eax
	mov eax, r13d
	add eax, r12d
	ror eax, 14
	xor r14d, eax
	mov eax, DWORD PTR [rsi+8]
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	mov eax, ecx
	add eax, DWORD PTR [rsi]
	ror eax, 25
	xor r10d, eax
	mov eax, r11d
	add eax, edx
	ror eax, 25
	xor r13d, eax
	mov eax, r14d
	add eax, ebx
	ror eax, 25
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, DWORD PTR [rsi+12]
	add eax, r15d
	ror eax, 25
	xor r9d, eax
	mov eax, r10d
	add eax, ecx
	ror eax, 23
	xor r12d, eax
	mov eax, r13d
	add eax, r11d
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, DWORD PTR [rsi+8]
	add eax, r14d
	ror eax, 23
	xor r8d, eax
	mov eax, r9d
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor ebp, eax
	mov eax, r12d
	add eax, r10d
	ror eax, 19
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, DWORD PTR [rsi+4]
	add eax, r13d
	ror eax, 19
	xor edx, eax
	mov eax, r8d
	add eax, DWORD PTR [rsi+8]
	ror eax, 19
	xor ebx, eax
	mov eax, ebp
	add eax, r9d
	ror eax, 19
	xor r15d, eax
	mov eax, DWORD PTR [rsi]
	add eax, r12d
	ror eax, 14
	xor ecx, eax
	mov eax, edx
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor r11d, eax
	mov eax, ebx
	add eax, r8d
	ror eax, 14
	xor r14d, eax
	mov eax, r15d
	add eax, ebp
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	mov eax, ecx
	add eax, r9d
	ror eax, 25
	xor edx, eax
	mov eax, r11d
	add eax, r10d
	ror eax, 25
	xor ebx, eax
	mov eax, r14d
	add eax, r13d
	ror eax, 25
	xor r15d, eax
	mov eax, DWORD PTR [rsi+12]
	add eax, DWORD PTR [rsi+8]
	ror eax, 25
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, edx
	add eax, ecx
	ror eax, 23
	xor r8d, eax
	mov eax, ebx
	add eax, r11d
	ror eax, 23
	xor ebp, eax
	mov eax, r15d
	add eax, r14d
	ror eax, 23
	xor r12d, eax
	mov eax, DWORD PTR [rsi]
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, r8d
	add eax, edx
	ror eax, 19
	xor r9d, eax
	mov eax, ebp
	add eax, ebx
	ror eax, 19
	xor r10d, eax
	mov eax, r12d
	add eax, r15d
	ror eax, 19
	xor r13d, eax
	mov eax, DWORD PTR [rsi+4]
	add eax, DWORD PTR [rsi]
	ror eax, 19
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, r9d
	add eax, r8d
	ror eax, 14
	xor ecx, eax
	mov eax, r10d
	add eax, ebp
	ror eax, 14
	xor r11d, eax
	mov eax, r13d
	add eax, r12d
	ror eax, 14
	xor r14d, eax
	mov eax, DWORD PTR [rsi+8]
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	mov eax, ecx
	add eax, DWORD PTR [rsi]
	ror eax, 25
	xor r10d, eax
	mov eax, r11d
	add eax, edx
	ror eax, 25
	xor r13d, eax
	mov eax, r14d
	add eax, ebx
	ror eax, 25
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, DWORD PTR [rsi+12]
	add eax, r15d
	ror eax, 25
	xor r9d, eax
	mov eax, r10d
	add eax, ecx
	ror eax, 23
	xor r12d, eax
	mov eax, r13d
	add eax, r11d
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, DWORD PTR [rsi+8]
	add eax, r14d
	ror eax, 23
	xor r8d, eax
	mov eax, r9d
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor ebp, eax
	mov eax, r12d
	add eax, r10d
	ror eax, 19
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, DWORD PTR [rsi+4]
	add eax, r13d
	ror eax, 19
	xor edx, eax
	mov eax, r8d
	add eax, DWORD PTR [rsi+8]
	ror eax, 19
	xor ebx, eax
	mov eax, ebp
	add eax, r9d
	ror eax, 19
	xor r15d, eax
	mov eax, DWORD PTR [rsi]
	add eax, r12d
	ror eax, 14
	xor ecx, eax
	mov eax, edx
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor r11d, eax
	mov eax, ebx
	add eax, r8d
	ror eax, 14
	xor r14d, eax
	mov eax, r15d
	add eax, ebp
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	mov eax, ecx
	add eax, r9d
	ror eax, 25
	xor edx, eax
	mov eax, r11d
	add eax, r10d
	ror eax, 25
	xor ebx, eax
	mov eax, r14d
	add eax, r13d
	ror eax, 25
	xor r15d, eax
	mov eax, DWORD PTR [rsi+12]
	add eax, DWORD PTR [rsi+8]
	ror eax, 25
	xor eax, DWORD PTR [rsi]
	mov DWORD PTR [rsi], eax
	mov eax, edx
	add eax, ecx
	ror eax, 23
	xor r8d, eax
	mov eax, ebx
	add eax, r11d
	ror eax, 23
	xor ebp, eax
	mov eax, r15d
	add eax, r14d
	ror eax, 23
	xor r12d, eax
	mov eax, DWORD PTR [rsi]
	add eax, DWORD PTR [rsi+12]
	ror eax, 23
	xor eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rsi+4], eax
	mov eax, r8d
	add eax, edx
	ror eax, 19
	xor r9d, eax
	mov eax, ebp
	add eax, ebx
	ror eax, 19
	xor r10d, eax
	mov eax, r12d
	add eax, r15d
	ror eax, 19
	xor r13d, eax
	mov eax, DWORD PTR [rsi+4]
	add eax, DWORD PTR [rsi]
	ror eax, 19
	xor eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rsi+8], eax
	mov eax, r9d
	add eax, r8d
	ror eax, 14
	xor ecx, eax
	mov eax, r10d
	add eax, ebp
	ror eax, 14
	xor r11d, eax
	mov eax, r13d
	add eax, r12d
	ror eax, 14
	xor r14d, eax
	mov eax, DWORD PTR [rsi+8]
	add eax, DWORD PTR [rsi+4]
	ror eax, 14
	xor eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rsi+12], eax
	add ecx, DWORD PTR [rdi]
	mov DWORD PTR [rdi], ecx
	add edx, DWORD PTR [rdi+4]
	mov DWORD PTR [rdi+4], edx
	add r8d, DWORD PTR [rdi+8]
	mov DWORD PTR [rdi+8], r8d
	add r9d, DWORD PTR [rdi+12]
	mov DWORD PTR [rdi+12], r9d
	add r10d, DWORD PTR [rdi+16]
	mov DWORD PTR [rdi+16], r10d
	add r11d, DWORD PTR [rdi+20]
	mov DWORD PTR [rdi+20], r11d
	add ebx, DWORD PTR [rdi+24]
	mov DWORD PTR [rdi+24], ebx
	add ebp, DWORD PTR [rdi+28]
	mov DWORD PTR [rdi+28], ebp
	add r12d, DWORD PTR [rdi+32]
	mov DWORD PTR [rdi+32], r12d
	add r13d, DWORD PTR [rdi+36]
	mov DWORD PTR [rdi+36], r13d
	add r14d, DWORD PTR [rdi+40]
	mov DWORD PTR [rdi+40], r14d
	add r15d, DWORD PTR [rdi+44]
	mov DWORD PTR [rdi+44], r15d
	mov eax, DWORD PTR [rsi]
	add eax, DWORD PTR [rdi+48]
	mov DWORD PTR [rdi+48], eax
	mov DWORD PTR [rsi], eax
	mov eax, DWORD PTR [rsi+4]
	add eax, DWORD PTR [rdi+52]
	mov DWORD PTR [rdi+52], eax
	mov DWORD PTR [rsi+4], eax
	mov eax, DWORD PTR [rsi+8]
	add eax, DWORD PTR [rdi+56]
	mov DWORD PTR [rdi+56], eax
	mov DWORD PTR [rsi+8], eax
	mov eax, DWORD PTR [rsi+12]
	add eax, DWORD PTR [rdi+60]
	mov DWORD PTR [rdi+60], eax
	mov DWORD PTR [rsi+12], eax
	mov rax, QWORD PTR [rsi+16]
	add rax, 128
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rsi+24]
	add rax, 64
	mov QWORD PTR [rsi+24], rax
	mov rax, QWORD PTR [rsi+32]
	add rax, 64
	mov QWORD PTR [rsi+32], rax
	mov rax, QWORD PTR [rsi+40]
	sub rax, 1
	mov QWORD PTR [rsi+40], rax
	jne 20b
	mov rbx, QWORD PTR [rsi+64]
	mov rbp, QWORD PTR [rsi+72]
	mov r12, QWORD PTR [rsi+80]
	mov r14, QWORD PTR [rsi+88]
	mov r15, QWORD PTR [rsi+96]
	mov r13, QWORD PTR [rsi+104]
	ret
	.p2align 6

vg_scrypt_romix:
	mov QWORD PTR [r8+128], rbx
	mov QWORD PTR [r8+136], rbp
	mov QWORD PTR [r8+144], r12
	mov QWORD PTR [r8+152], r14
	mov QWORD PTR [r8+160], r15
	mov QWORD PTR [r8+168], r13
	mov rbx, rdi
	mov r12, rdx
	mov r13, r8
	mov r14, rsi
	add r14, r14
	add r14, r14
	add r14, r14
	add r14, r14
	add r14, r14
	add r14, r14
	add r14, r14
	mov rax, rsi
	mov edx, 1
	add rcx, rcx
20:
	add rax, rax
	add rdx, rdx
	cmp rax, rcx
	jne 20b
	shr rdx, 1
	mov QWORD PTR [r13+176], rdx
	mov r15, rdx
	mov rbp, r12
	mov rdi, rbx
	mov rsi, rbp
	mov rcx, r14
	shr rcx, 4
21:
	movdqu xmm0, XMMWORD PTR [rdi]
	movdqu XMMWORD PTR [rsi], xmm0
	add rdi, 16
	add rsi, 16
	sub rcx, 1
	jne 21b
22:
	mov rdi, rbp
	mov rsi, r14
	shr rsi, 7
	mov rcx, rsi
	mov rdx, rbp
	add rdx, r14
	mov r8, r13
	cmp r15, 1
	je 23f
	jmp 24f
23:
	mov rdx, rbx
24:
	call {vg_scrypt_blockmix}
	add rbp, r14
	sub r15, 1
	jne 22b
	mov r15, QWORD PTR [r13+176]
	mov rbp, r15
	sub rbp, 1
25:
	mov rax, QWORD PTR [rbx+r14*1-64]
	and rax, rbp
	mov rdx, r12
	mov rcx, r14
	mov rdi, rdx
	mul rcx
	mov rdx, rdi
	add rdx, rax
	mov rdi, rbx
	mov rsi, rdx
	mov r8, r13
	add r8, 192
	mov rcx, r14
	shr rcx, 4
26:
	movdqu xmm0, XMMWORD PTR [rdi]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r8], xmm0
	add rdi, 16
	add rsi, 16
	add r8, 16
	sub rcx, 1
	jne 26b
	mov rdi, r13
	add rdi, 192
	mov rsi, r14
	shr rsi, 7
	mov rcx, rsi
	mov rdx, rbx
	mov r8, r13
	call {vg_scrypt_blockmix}
	sub r15, 1
	jne 25b
	mov rbx, QWORD PTR [r13+128]
	mov rbp, QWORD PTR [r13+136]
	mov r12, QWORD PTR [r13+144]
	mov r14, QWORD PTR [r13+152]
	mov r15, QWORD PTR [r13+160]
	mov r13, QWORD PTR [r13+168]
	ret
	.p2align 6

vg_scrypt:
	push r9
	push r8
	push rsi
	push rdi
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+64]
	ror rax, 57
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch}
	mov rax, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
20:
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+80]
	mov r8, QWORD PTR [rsp+88]
	mov r9, rsi
	add r9, 2
	call {vg_scrypt_romix}
	mov rcx, QWORD PTR [rsp+40]
	ror rcx, 57
	mov rax, QWORD PTR [rsp+16]
	add rax, rcx
	mov rdx, QWORD PTR [rsp+64]
	ror rdx, 57
	add rdx, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
	cmp rax, rdx
	jne 20b
	mov rdi, QWORD PTR [rsp+24]
	mov rsi, QWORD PTR [rsp+32]
	mov rdx, QWORD PTR [rsp+48]
	mov rcx, QWORD PTR [rsp+64]
	ror rcx, 57
	mov r9, QWORD PTR [rsp+104]
	mov rax, QWORD PTR [rsp+112]
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	ret
	.p2align 6

vg_scrypt_avx2:
	push r9
	push r8
	push rsi
	push rdi
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+64]
	ror rax, 57
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch_avx2}
	mov rax, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
20:
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+80]
	mov r8, QWORD PTR [rsp+88]
	mov r9, rsi
	add r9, 2
	call {vg_scrypt_romix}
	mov rcx, QWORD PTR [rsp+40]
	ror rcx, 57
	mov rax, QWORD PTR [rsp+16]
	add rax, rcx
	mov rdx, QWORD PTR [rsp+64]
	ror rdx, 57
	add rdx, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
	cmp rax, rdx
	jne 20b
	mov rdi, QWORD PTR [rsp+24]
	mov rsi, QWORD PTR [rsp+32]
	mov rdx, QWORD PTR [rsp+48]
	mov rcx, QWORD PTR [rsp+64]
	ror rcx, 57
	mov r9, QWORD PTR [rsp+104]
	mov rax, QWORD PTR [rsp+112]
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch_avx2}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	ret
	.p2align 6

vg_scrypt_shani:
	push r9
	push r8
	push rsi
	push rdi
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+64]
	ror rax, 57
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch_shani}
	mov rax, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
20:
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+80]
	mov r8, QWORD PTR [rsp+88]
	mov r9, rsi
	add r9, 2
	call {vg_scrypt_romix}
	mov rcx, QWORD PTR [rsp+40]
	ror rcx, 57
	mov rax, QWORD PTR [rsp+16]
	add rax, rcx
	mov rdx, QWORD PTR [rsp+64]
	ror rdx, 57
	add rdx, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
	cmp rax, rdx
	jne 20b
	mov rdi, QWORD PTR [rsp+24]
	mov rsi, QWORD PTR [rsp+32]
	mov rdx, QWORD PTR [rsp+48]
	mov rcx, QWORD PTR [rsp+64]
	ror rcx, 57
	mov r9, QWORD PTR [rsp+104]
	mov rax, QWORD PTR [rsp+112]
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch_shani}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	ret
	.p2align 6
