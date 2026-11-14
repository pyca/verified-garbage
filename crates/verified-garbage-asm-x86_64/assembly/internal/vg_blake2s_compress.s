// The functions of `src/internal/vg_blake2s_compress.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2s_compress:
	mov QWORD PTR [r9+296], rbx
	mov QWORD PTR [r9+304], rbp
	mov QWORD PTR [r9+312], r12
	mov QWORD PTR [r9+320], r13
	mov QWORD PTR [r9+328], r14
	mov QWORD PTR [r9+336], r15
	mov r8d, r8d
	mov QWORD PTR [r9+256], rsi
	mov QWORD PTR [r9+264], rdx
	mov QWORD PTR [r9+272], rcx
	mov eax, 0
	mov QWORD PTR [r9+280], rax
	test r8, r8
	je 20f
	mov rax, -1
	jmp 21f
20:
21:
	mov QWORD PTR [r9+288], rax
	test rdx, rdx
	je 22f
24:
	mov rsi, QWORD PTR [r9+256]
	mov eax, DWORD PTR [rsi]
	mov DWORD PTR [r9], eax
	mov eax, DWORD PTR [rsi+4]
	mov DWORD PTR [r9+4], eax
	mov eax, DWORD PTR [rsi+8]
	mov DWORD PTR [r9+8], eax
	mov eax, DWORD PTR [rsi+12]
	mov DWORD PTR [r9+12], eax
	mov eax, DWORD PTR [rsi+16]
	mov DWORD PTR [r9+16], eax
	mov eax, DWORD PTR [rsi+20]
	mov DWORD PTR [r9+20], eax
	mov eax, DWORD PTR [rsi+24]
	mov DWORD PTR [r9+24], eax
	mov eax, DWORD PTR [rsi+28]
	mov DWORD PTR [r9+28], eax
	mov eax, DWORD PTR [rsi+32]
	mov DWORD PTR [r9+32], eax
	mov eax, DWORD PTR [rsi+36]
	mov DWORD PTR [r9+36], eax
	mov eax, DWORD PTR [rsi+40]
	mov DWORD PTR [r9+40], eax
	mov eax, DWORD PTR [rsi+44]
	mov DWORD PTR [r9+44], eax
	mov eax, DWORD PTR [rsi+48]
	mov DWORD PTR [r9+48], eax
	mov eax, DWORD PTR [rsi+52]
	mov DWORD PTR [r9+52], eax
	mov eax, DWORD PTR [rsi+56]
	mov DWORD PTR [r9+56], eax
	mov eax, DWORD PTR [rsi+60]
	mov DWORD PTR [r9+60], eax
	mov eax, 1779033703
	mov DWORD PTR [r9+192], eax
	mov eax, -1150833019
	mov DWORD PTR [r9+200], eax
	mov eax, 1013904242
	mov DWORD PTR [r9+208], eax
	mov eax, -1521486534
	mov DWORD PTR [r9+216], eax
	mov eax, DWORD PTR [rdi]
	mov ebx, DWORD PTR [rdi+4]
	mov ecx, DWORD PTR [rdi+8]
	mov edx, DWORD PTR [rdi+12]
	mov r14d, DWORD PTR [rdi+16]
	mov r15d, DWORD PTR [rdi+20]
	mov ebp, DWORD PTR [rdi+24]
	mov r8d, DWORD PTR [rdi+28]
	mov r10d, 1359893119
	xor r10d, DWORD PTR [r9+272]
	mov r11d, -1694144372
	xor r11d, DWORD PTR [r9+276]
	mov r12d, 528734635
	xor r12d, DWORD PTR [r9+288]
	mov r13d, 1541459225
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9]
	add eax, r14d
	xor r10d, eax
	ror r10d, 16
	add esi, r10d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+8]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 16
	add esi, r11d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+16]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 16
	add esi, r12d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+24]
	add edx, r8d
	xor r13d, edx
	ror r13d, 16
	add esi, r13d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+4]
	add eax, r14d
	xor r10d, eax
	ror r10d, 8
	add esi, r10d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+12]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 8
	add esi, r11d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+20]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 8
	add esi, r12d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+28]
	add edx, r8d
	xor r13d, edx
	ror r13d, 8
	add esi, r13d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+32]
	add eax, r15d
	xor r13d, eax
	ror r13d, 16
	add esi, r13d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+40]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 16
	add esi, r10d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+48]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 16
	add esi, r11d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+56]
	add edx, r14d
	xor r12d, edx
	ror r12d, 16
	add esi, r12d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+36]
	add eax, r15d
	xor r13d, eax
	ror r13d, 8
	add esi, r13d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+44]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 8
	add esi, r10d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+52]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 8
	add esi, r11d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+60]
	add edx, r14d
	xor r12d, edx
	ror r12d, 8
	add esi, r12d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+56]
	add eax, r14d
	xor r10d, eax
	ror r10d, 16
	add esi, r10d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+16]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 16
	add esi, r11d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+36]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 16
	add esi, r12d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+52]
	add edx, r8d
	xor r13d, edx
	ror r13d, 16
	add esi, r13d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+40]
	add eax, r14d
	xor r10d, eax
	ror r10d, 8
	add esi, r10d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+32]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 8
	add esi, r11d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+60]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 8
	add esi, r12d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+24]
	add edx, r8d
	xor r13d, edx
	ror r13d, 8
	add esi, r13d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+4]
	add eax, r15d
	xor r13d, eax
	ror r13d, 16
	add esi, r13d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 16
	add esi, r10d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+44]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 16
	add esi, r11d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+20]
	add edx, r14d
	xor r12d, edx
	ror r12d, 16
	add esi, r12d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+48]
	add eax, r15d
	xor r13d, eax
	ror r13d, 8
	add esi, r13d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+8]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 8
	add esi, r10d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+28]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 8
	add esi, r11d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+12]
	add edx, r14d
	xor r12d, edx
	ror r12d, 8
	add esi, r12d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+44]
	add eax, r14d
	xor r10d, eax
	ror r10d, 16
	add esi, r10d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+48]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 16
	add esi, r11d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+20]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 16
	add esi, r12d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+60]
	add edx, r8d
	xor r13d, edx
	ror r13d, 16
	add esi, r13d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+32]
	add eax, r14d
	xor r10d, eax
	ror r10d, 8
	add esi, r10d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 8
	add esi, r11d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+8]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 8
	add esi, r12d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+52]
	add edx, r8d
	xor r13d, edx
	ror r13d, 8
	add esi, r13d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+40]
	add eax, r15d
	xor r13d, eax
	ror r13d, 16
	add esi, r13d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+12]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 16
	add esi, r10d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+28]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 16
	add esi, r11d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+36]
	add edx, r14d
	xor r12d, edx
	ror r12d, 16
	add esi, r12d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+56]
	add eax, r15d
	xor r13d, eax
	ror r13d, 8
	add esi, r13d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+24]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 8
	add esi, r10d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+4]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 8
	add esi, r11d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+16]
	add edx, r14d
	xor r12d, edx
	ror r12d, 8
	add esi, r12d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+28]
	add eax, r14d
	xor r10d, eax
	ror r10d, 16
	add esi, r10d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+12]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 16
	add esi, r11d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+52]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 16
	add esi, r12d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+44]
	add edx, r8d
	xor r13d, edx
	ror r13d, 16
	add esi, r13d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+36]
	add eax, r14d
	xor r10d, eax
	ror r10d, 8
	add esi, r10d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+4]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 8
	add esi, r11d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+48]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 8
	add esi, r12d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+56]
	add edx, r8d
	xor r13d, edx
	ror r13d, 8
	add esi, r13d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+8]
	add eax, r15d
	xor r13d, eax
	ror r13d, 16
	add esi, r13d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+20]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 16
	add esi, r10d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+16]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 16
	add esi, r11d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+60]
	add edx, r14d
	xor r12d, edx
	ror r12d, 16
	add esi, r12d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+24]
	add eax, r15d
	xor r13d, eax
	ror r13d, 8
	add esi, r13d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+40]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 8
	add esi, r10d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 8
	add esi, r11d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+32]
	add edx, r14d
	xor r12d, edx
	ror r12d, 8
	add esi, r12d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+36]
	add eax, r14d
	xor r10d, eax
	ror r10d, 16
	add esi, r10d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+20]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 16
	add esi, r11d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+8]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 16
	add esi, r12d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+40]
	add edx, r8d
	xor r13d, edx
	ror r13d, 16
	add esi, r13d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9]
	add eax, r14d
	xor r10d, eax
	ror r10d, 8
	add esi, r10d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+28]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 8
	add esi, r11d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+16]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 8
	add esi, r12d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+60]
	add edx, r8d
	xor r13d, edx
	ror r13d, 8
	add esi, r13d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+56]
	add eax, r15d
	xor r13d, eax
	ror r13d, 16
	add esi, r13d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+44]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 16
	add esi, r10d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+24]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 16
	add esi, r11d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+12]
	add edx, r14d
	xor r12d, edx
	ror r12d, 16
	add esi, r12d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+4]
	add eax, r15d
	xor r13d, eax
	ror r13d, 8
	add esi, r13d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+48]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 8
	add esi, r10d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+32]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 8
	add esi, r11d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+52]
	add edx, r14d
	xor r12d, edx
	ror r12d, 8
	add esi, r12d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+8]
	add eax, r14d
	xor r10d, eax
	ror r10d, 16
	add esi, r10d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+24]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 16
	add esi, r11d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 16
	add esi, r12d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+32]
	add edx, r8d
	xor r13d, edx
	ror r13d, 16
	add esi, r13d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+48]
	add eax, r14d
	xor r10d, eax
	ror r10d, 8
	add esi, r10d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+40]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 8
	add esi, r11d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+44]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 8
	add esi, r12d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+12]
	add edx, r8d
	xor r13d, edx
	ror r13d, 8
	add esi, r13d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+16]
	add eax, r15d
	xor r13d, eax
	ror r13d, 16
	add esi, r13d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+28]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 16
	add esi, r10d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+60]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 16
	add esi, r11d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+4]
	add edx, r14d
	xor r12d, edx
	ror r12d, 16
	add esi, r12d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+52]
	add eax, r15d
	xor r13d, eax
	ror r13d, 8
	add esi, r13d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+20]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 8
	add esi, r10d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+56]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 8
	add esi, r11d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+36]
	add edx, r14d
	xor r12d, edx
	ror r12d, 8
	add esi, r12d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+48]
	add eax, r14d
	xor r10d, eax
	ror r10d, 16
	add esi, r10d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+4]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 16
	add esi, r11d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+56]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 16
	add esi, r12d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+16]
	add edx, r8d
	xor r13d, edx
	ror r13d, 16
	add esi, r13d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+20]
	add eax, r14d
	xor r10d, eax
	ror r10d, 8
	add esi, r10d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+60]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 8
	add esi, r11d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+52]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 8
	add esi, r12d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+40]
	add edx, r8d
	xor r13d, edx
	ror r13d, 8
	add esi, r13d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9]
	add eax, r15d
	xor r13d, eax
	ror r13d, 16
	add esi, r13d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+24]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 16
	add esi, r10d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+36]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 16
	add esi, r11d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+32]
	add edx, r14d
	xor r12d, edx
	ror r12d, 16
	add esi, r12d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+28]
	add eax, r15d
	xor r13d, eax
	ror r13d, 8
	add esi, r13d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+12]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 8
	add esi, r10d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+8]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 8
	add esi, r11d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+44]
	add edx, r14d
	xor r12d, edx
	ror r12d, 8
	add esi, r12d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+52]
	add eax, r14d
	xor r10d, eax
	ror r10d, 16
	add esi, r10d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+28]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 16
	add esi, r11d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+48]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 16
	add esi, r12d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+12]
	add edx, r8d
	xor r13d, edx
	ror r13d, 16
	add esi, r13d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+44]
	add eax, r14d
	xor r10d, eax
	ror r10d, 8
	add esi, r10d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+56]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 8
	add esi, r11d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+4]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 8
	add esi, r12d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+36]
	add edx, r8d
	xor r13d, edx
	ror r13d, 8
	add esi, r13d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+20]
	add eax, r15d
	xor r13d, eax
	ror r13d, 16
	add esi, r13d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+60]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 16
	add esi, r10d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+32]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 16
	add esi, r11d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+8]
	add edx, r14d
	xor r12d, edx
	ror r12d, 16
	add esi, r12d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9]
	add eax, r15d
	xor r13d, eax
	ror r13d, 8
	add esi, r13d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+16]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 8
	add esi, r10d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+24]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 8
	add esi, r11d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+40]
	add edx, r14d
	xor r12d, edx
	ror r12d, 8
	add esi, r12d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+24]
	add eax, r14d
	xor r10d, eax
	ror r10d, 16
	add esi, r10d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+56]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 16
	add esi, r11d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+44]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 16
	add esi, r12d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9]
	add edx, r8d
	xor r13d, edx
	ror r13d, 16
	add esi, r13d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+60]
	add eax, r14d
	xor r10d, eax
	ror r10d, 8
	add esi, r10d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+36]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 8
	add esi, r11d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+12]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 8
	add esi, r12d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+32]
	add edx, r8d
	xor r13d, edx
	ror r13d, 8
	add esi, r13d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+48]
	add eax, r15d
	xor r13d, eax
	ror r13d, 16
	add esi, r13d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+52]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 16
	add esi, r10d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+4]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 16
	add esi, r11d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+40]
	add edx, r14d
	xor r12d, edx
	ror r12d, 16
	add esi, r12d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+8]
	add eax, r15d
	xor r13d, eax
	ror r13d, 8
	add esi, r13d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+28]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 8
	add esi, r10d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+16]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 8
	add esi, r11d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+20]
	add edx, r14d
	xor r12d, edx
	ror r12d, 8
	add esi, r12d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+40]
	add eax, r14d
	xor r10d, eax
	ror r10d, 16
	add esi, r10d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+32]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 16
	add esi, r11d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+28]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 16
	add esi, r12d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+4]
	add edx, r8d
	xor r13d, edx
	ror r13d, 16
	add esi, r13d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add eax, DWORD PTR [r9+8]
	add eax, r14d
	xor r10d, eax
	ror r10d, 8
	add esi, r10d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add ebx, DWORD PTR [r9+16]
	add ebx, r15d
	xor r11d, ebx
	ror r11d, 8
	add esi, r11d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add ecx, DWORD PTR [r9+24]
	add ecx, ebp
	xor r12d, ecx
	ror r12d, 8
	add esi, r12d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add edx, DWORD PTR [r9+20]
	add edx, r8d
	xor r13d, edx
	ror r13d, 8
	add esi, r13d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+60]
	add eax, r15d
	xor r13d, eax
	ror r13d, 16
	add esi, r13d
	xor r15d, esi
	ror r15d, 12
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+36]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 16
	add esi, r10d
	xor ebp, esi
	ror ebp, 12
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+12]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 16
	add esi, r11d
	xor r8d, esi
	ror r8d, 12
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9+52]
	add edx, r14d
	xor r12d, edx
	ror r12d, 16
	add esi, r12d
	xor r14d, esi
	ror r14d, 12
	mov DWORD PTR [r9+200], esi
	mov esi, DWORD PTR [r9+208]
	add eax, DWORD PTR [r9+44]
	add eax, r15d
	xor r13d, eax
	ror r13d, 8
	add esi, r13d
	xor r15d, esi
	ror r15d, 7
	mov DWORD PTR [r9+208], esi
	mov esi, DWORD PTR [r9+216]
	add ebx, DWORD PTR [r9+56]
	add ebx, ebp
	xor r10d, ebx
	ror r10d, 8
	add esi, r10d
	xor ebp, esi
	ror ebp, 7
	mov DWORD PTR [r9+216], esi
	mov esi, DWORD PTR [r9+192]
	add ecx, DWORD PTR [r9+48]
	add ecx, r8d
	xor r11d, ecx
	ror r11d, 8
	add esi, r11d
	xor r8d, esi
	ror r8d, 7
	mov DWORD PTR [r9+192], esi
	mov esi, DWORD PTR [r9+200]
	add edx, DWORD PTR [r9]
	add edx, r14d
	xor r12d, edx
	ror r12d, 8
	add esi, r12d
	xor r14d, esi
	ror r14d, 7
	mov DWORD PTR [r9+200], esi
	mov DWORD PTR [r9+224], r10d
	mov DWORD PTR [r9+232], r11d
	mov DWORD PTR [r9+240], r12d
	mov DWORD PTR [r9+248], r13d
	xor eax, DWORD PTR [r9+192]
	xor eax, DWORD PTR [rdi]
	mov DWORD PTR [rdi], eax
	xor ebx, DWORD PTR [r9+200]
	xor ebx, DWORD PTR [rdi+4]
	mov DWORD PTR [rdi+4], ebx
	xor ecx, DWORD PTR [r9+208]
	xor ecx, DWORD PTR [rdi+8]
	mov DWORD PTR [rdi+8], ecx
	xor edx, DWORD PTR [r9+216]
	xor edx, DWORD PTR [rdi+12]
	mov DWORD PTR [rdi+12], edx
	xor r14d, DWORD PTR [r9+224]
	xor r14d, DWORD PTR [rdi+16]
	mov DWORD PTR [rdi+16], r14d
	xor r15d, DWORD PTR [r9+232]
	xor r15d, DWORD PTR [rdi+20]
	mov DWORD PTR [rdi+20], r15d
	xor ebp, DWORD PTR [r9+240]
	xor ebp, DWORD PTR [rdi+24]
	mov DWORD PTR [rdi+24], ebp
	xor r8d, DWORD PTR [r9+248]
	xor r8d, DWORD PTR [rdi+28]
	mov DWORD PTR [rdi+28], r8d
	mov rsi, QWORD PTR [r9+256]
	add rsi, 64
	mov QWORD PTR [r9+256], rsi
	mov rcx, QWORD PTR [r9+272]
	add rcx, 64
	mov QWORD PTR [r9+272], rcx
	mov rdx, QWORD PTR [r9+264]
	sub rdx, 1
	mov QWORD PTR [r9+264], rdx
	jne 24b
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r9+296]
	mov rbp, QWORD PTR [r9+304]
	mov r12, QWORD PTR [r9+312]
	mov r13, QWORD PTR [r9+320]
	mov r14, QWORD PTR [r9+328]
	mov r15, QWORD PTR [r9+336]
	ret
	.p2align 6
