// The functions of `src/argon2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_argon2_blake2b_avx2_g_avx2:
	push rbx
	push rbp
	push r12
	push r13
	push r14
	push r15
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+264], rax
	mov rbp, rsp
	mov edi, edi
	mov r9d, r9d
	mov QWORD PTR [rbp+72], r9
	mov QWORD PTR [rbp+80], r8
	mov QWORD PTR [rbp+88], rcx
	mov QWORD PTR [rbp+96], rdx
	mov QWORD PTR [rbp+104], rsi
	mov QWORD PTR [rbp+112], rdi
	mov rbx, QWORD PTR [rbp+248]
	mov rax, QWORD PTR [rbp+176]
	mov eax, eax
	mov QWORD PTR [rbp+176], rax
	mov rax, QWORD PTR [rbp+184]
	mov eax, eax
	mov QWORD PTR [rbp+184], rax
	mov rax, QWORD PTR [rbp+192]
	mov eax, eax
	mov QWORD PTR [rbp+192], rax
	mov rdi, QWORD PTR [rbp+176]
	mov rsi, QWORD PTR [rbp+184]
	add rsi, rsi
	add rsi, rsi
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r13, r9
	add r13, r13
	add r13, r13
	mov esi, 64
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 832
	mov ecx, 0
	call {vg_blake2b_init}
	mov rax, QWORD PTR [rbp+184]
	mov DWORD PTR [rbx+768], eax
	mov rax, QWORD PTR [rbp+264]
	mov DWORD PTR [rbx+772], eax
	mov rax, QWORD PTR [rbp+176]
	mov DWORD PTR [rbx+776], eax
	mov rax, QWORD PTR [rbp+72]
	mov DWORD PTR [rbx+780], eax
	mov eax, 19
	mov DWORD PTR [rbx+784], eax
	mov rax, QWORD PTR [rbp+112]
	mov DWORD PTR [rbx+788], eax
	mov esi, 0
	mov rdx, rbx
	add rdx, 768
	mov ecx, 24
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	mov r12d, 24
	mov r14, QWORD PTR [rbp+96]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+104]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, r14
	mov r14, QWORD PTR [rbp+80]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+88]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, r14
	mov r14, QWORD PTR [rbp+208]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+200]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, r14
	mov r14, QWORD PTR [rbp+224]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+216]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, r14
	mov rsi, r12
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 768
	mov rcx, rbx
	add rcx, 192
	call {vg_blake2b_finalize_scratch_avx2}
	mov r14, rbp
	mov eax, 64
	mov rdx, rbx
	add rdx, 768
20:
	movzx ecx, BYTE PTR [rdx]
	mov BYTE PTR [r14], cl
	add rdx, 1
	add r14, 1
	sub rax, 1
	jne 20b
	mov r14, QWORD PTR [rbp+232]
	mov rax, QWORD PTR [rbp+240]
	mov ecx, 0
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
21:
	mov QWORD PTR [r14], rcx
	add r14, 8
	sub rax, 1
	jne 21b
	mov r14, QWORD PTR [rbp+232]
	mov r12d, 0
	mov r15, QWORD PTR [rbp+184]
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
22:
	mov eax, 0
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime_avx2}
	add r14, 1024
	mov eax, 1
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime_avx2}
	add r14, r13
	sub r14, 1024
	add r12, 1
	sub r15, 1
	jne 22b
	mov r12, r13
	shr r12, 10
	shr r13, 12
	mov rax, 0
	mov QWORD PTR [rbp], rax
	mov rbx, 0
	mov r14, 0
23:
	mov r14, 0
24:
	mov rbx, 0
25:
	mov rax, 0
	mov QWORD PTR [rbp+8], rax
	mov rcx, QWORD PTR [rbp]
	or rcx, r14
	cmp rcx, 0
	je 26f
	mov r15, 0
	jmp 27f
26:
	mov r15, 2
27:
	cmp r15, r13
	jb 28f
	jmp 29f
28:
210:
	mov rax, QWORD PTR [rbp+112]
	mov r10, rax
	xor r10, 1
	cmp r10, 1
	sbb r10, r10
	mov r8, rax
	xor r8, 2
	cmp r8, 1
	sbb r8, r8
	mov r9, QWORD PTR [rbp]
	cmp r9, 1
	sbb r9, r9
	cmp r14, 2
	sbb r11, r11
	and r8, r9
	and r8, r11
	or r10, r8
	and r10, 1
	cmp r10, 0
	je 211f
	mov rax, r15
	shr rax, 7
	add rax, 1
	cmp rax, QWORD PTR [rbp+8]
	je 213f
	mov QWORD PTR [rbp+8], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 7168
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, QWORD PTR [rbp]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], r14
	mov rax, QWORD PTR [rbp+240]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rbp+72]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rbp+112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rbp+8]
	mov QWORD PTR [rdi+48], rax
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 5120
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress_avx2}
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 4096
	mov rdx, rcx
	add rdx, 6144
	call {vg_argon2_compress_avx2}
	jmp 214f
213:
214:
	mov rcx, QWORD PTR [rbp+248]
	mov rax, r15
	and rax, 127
	mov rdi, QWORD PTR [rcx+rax*8+6144]
	jmp 212f
211:
	mov r8, QWORD PTR [rbp+232]
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 215f
	mov rdi, rcx
	jmp 216f
215:
	mov rdi, r12
216:
	sub rdi, 1
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rdi, QWORD PTR [rax]
212:
	mov rsi, QWORD PTR [rbp+184]
	mov r11, rdi
	shr rdi, 32
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r9, QWORD PTR [rbp]
	mov rax, r9
	or rax, r14
	je 217f
	jmp 218f
217:
	mov r8, rbx
218:
	mov rdi, r8
	mov rsi, rbx
	cmp r9, 0
	je 219f
	mov rax, r14
	add rax, 1
	mul r13
	mov r10, rax
	cmp r14, 3
	je 221f
	jmp 222f
221:
	mov r10, 0
222:
	jmp 220f
219:
	mov r10, 0
220:
	cmp r9, 0
	je 223f
	mov rax, r12
	sub rax, r13
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
	jmp 224f
223:
	mov rax, r13
	mul r14
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
224:
	mov r8, r15
	sub r8, 1
	sbb r9, r9
	add rcx, r9
	mov rax, rdi
	xor rax, rsi
	sub rax, 1
	sbb rax, rax
	mov r8, rcx
	xor rdx, rcx
	and rdx, rax
	xor r8, rdx
	mov r9, rdi
	mov rdi, r11
	mov rsi, r8
	mov eax, edi
	mul rax
	shr rax, 32
	mul rsi
	shr rax, 32
	mov rcx, rsi
	sub rcx, 1
	sub rcx, rax
	mov rax, rcx
	mov rdi, rax
	add rdi, r10
	mov rsi, r12
	mov r10, rdi
	sub rdi, rsi
	sbb rax, rax
	xor r10, rdi
	and r10, rax
	xor rdi, r10
	mov r8, QWORD PTR [rbp+232]
	mov rsi, rdi
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 225f
	mov rdi, rcx
	jmp 226f
225:
	mov rdi, r12
226:
	sub rdi, 1
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r10, rax
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r11, rax
	mov rcx, rsi
	mov rax, r9
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r11
	mov QWORD PTR [rbp+16], r10
	mov rcx, QWORD PTR [rbp+248]
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress_avx2}
	mov rdi, QWORD PTR [rbp+16]
	mov rsi, QWORD PTR [rbp+248]
	add rsi, 4096
	mov r9, QWORD PTR [rbp]
	cmp r9, 0
	je 227f
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	jmp 228f
227:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	mov QWORD PTR [rdi+1016], rax
228:
	add r15, 1
	cmp r15, r13
	jb 210b
29:
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 25b
	add r14, 1
	cmp r14, 4
	jb 24b
	mov rax, QWORD PTR [rbp]
	add rax, 1
	mov QWORD PTR [rbp], rax
	cmp rax, QWORD PTR [rbp+72]
	jb 23b
	mov rdi, QWORD PTR [rbp+232]
	mov rbx, 0
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
229:
	mov r8, QWORD PTR [rbp+232]
	mov rax, rbx
	mov rcx, r12
	sub rcx, 1
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r8
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 229b
	mov rdi, QWORD PTR [rbp+232]
	mov rsi, 1024
	mov rdx, QWORD PTR [rbp+256]
	mov rcx, QWORD PTR [rbp+264]
	mov r8, QWORD PTR [rbp+248]
	call {vg_argon2_hprime_avx2}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop r15
	pop r14
	pop r13
	pop r12
	pop rbp
	pop rbx
	ret
	.p2align 6

vg_argon2_blake2b_avx2_g_avx512:
	push rbx
	push rbp
	push r12
	push r13
	push r14
	push r15
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+264], rax
	mov rbp, rsp
	mov edi, edi
	mov r9d, r9d
	mov QWORD PTR [rbp+72], r9
	mov QWORD PTR [rbp+80], r8
	mov QWORD PTR [rbp+88], rcx
	mov QWORD PTR [rbp+96], rdx
	mov QWORD PTR [rbp+104], rsi
	mov QWORD PTR [rbp+112], rdi
	mov rbx, QWORD PTR [rbp+248]
	mov rax, QWORD PTR [rbp+176]
	mov eax, eax
	mov QWORD PTR [rbp+176], rax
	mov rax, QWORD PTR [rbp+184]
	mov eax, eax
	mov QWORD PTR [rbp+184], rax
	mov rax, QWORD PTR [rbp+192]
	mov eax, eax
	mov QWORD PTR [rbp+192], rax
	mov rdi, QWORD PTR [rbp+176]
	mov rsi, QWORD PTR [rbp+184]
	add rsi, rsi
	add rsi, rsi
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r13, r9
	add r13, r13
	add r13, r13
	mov esi, 64
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 832
	mov ecx, 0
	call {vg_blake2b_init}
	mov rax, QWORD PTR [rbp+184]
	mov DWORD PTR [rbx+768], eax
	mov rax, QWORD PTR [rbp+264]
	mov DWORD PTR [rbx+772], eax
	mov rax, QWORD PTR [rbp+176]
	mov DWORD PTR [rbx+776], eax
	mov rax, QWORD PTR [rbp+72]
	mov DWORD PTR [rbx+780], eax
	mov eax, 19
	mov DWORD PTR [rbx+784], eax
	mov rax, QWORD PTR [rbp+112]
	mov DWORD PTR [rbx+788], eax
	mov esi, 0
	mov rdx, rbx
	add rdx, 768
	mov ecx, 24
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	mov r12d, 24
	mov r14, QWORD PTR [rbp+96]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+104]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, r14
	mov r14, QWORD PTR [rbp+80]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+88]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, r14
	mov r14, QWORD PTR [rbp+208]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+200]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, r14
	mov r14, QWORD PTR [rbp+224]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+216]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, r14
	mov rsi, r12
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 768
	mov rcx, rbx
	add rcx, 192
	call {vg_blake2b_finalize_scratch_avx2}
	mov r14, rbp
	mov eax, 64
	mov rdx, rbx
	add rdx, 768
20:
	movzx ecx, BYTE PTR [rdx]
	mov BYTE PTR [r14], cl
	add rdx, 1
	add r14, 1
	sub rax, 1
	jne 20b
	mov r14, QWORD PTR [rbp+232]
	mov rax, QWORD PTR [rbp+240]
	mov ecx, 0
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
21:
	mov QWORD PTR [r14], rcx
	add r14, 8
	sub rax, 1
	jne 21b
	mov r14, QWORD PTR [rbp+232]
	mov r12d, 0
	mov r15, QWORD PTR [rbp+184]
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
22:
	mov eax, 0
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime_avx2}
	add r14, 1024
	mov eax, 1
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime_avx2}
	add r14, r13
	sub r14, 1024
	add r12, 1
	sub r15, 1
	jne 22b
	mov r12, r13
	shr r12, 10
	shr r13, 12
	mov rax, 0
	mov QWORD PTR [rbp], rax
	mov rbx, 0
	mov r14, 0
23:
	mov r14, 0
24:
	mov rbx, 0
25:
	mov rax, 0
	mov QWORD PTR [rbp+8], rax
	mov rcx, QWORD PTR [rbp]
	or rcx, r14
	cmp rcx, 0
	je 26f
	mov r15, 0
	jmp 27f
26:
	mov r15, 2
27:
	cmp r15, r13
	jb 28f
	jmp 29f
28:
210:
	mov rax, QWORD PTR [rbp+112]
	mov r10, rax
	xor r10, 1
	cmp r10, 1
	sbb r10, r10
	mov r8, rax
	xor r8, 2
	cmp r8, 1
	sbb r8, r8
	mov r9, QWORD PTR [rbp]
	cmp r9, 1
	sbb r9, r9
	cmp r14, 2
	sbb r11, r11
	and r8, r9
	and r8, r11
	or r10, r8
	and r10, 1
	cmp r10, 0
	je 211f
	mov rax, r15
	shr rax, 7
	add rax, 1
	cmp rax, QWORD PTR [rbp+8]
	je 213f
	mov QWORD PTR [rbp+8], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 7168
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, QWORD PTR [rbp]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], r14
	mov rax, QWORD PTR [rbp+240]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rbp+72]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rbp+112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rbp+8]
	mov QWORD PTR [rdi+48], rax
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 5120
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress_avx512}
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 4096
	mov rdx, rcx
	add rdx, 6144
	call {vg_argon2_compress_avx512}
	jmp 214f
213:
214:
	mov rcx, QWORD PTR [rbp+248]
	mov rax, r15
	and rax, 127
	mov rdi, QWORD PTR [rcx+rax*8+6144]
	jmp 212f
211:
	mov r8, QWORD PTR [rbp+232]
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 215f
	mov rdi, rcx
	jmp 216f
215:
	mov rdi, r12
216:
	sub rdi, 1
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rdi, QWORD PTR [rax]
212:
	mov rsi, QWORD PTR [rbp+184]
	mov r11, rdi
	shr rdi, 32
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r9, QWORD PTR [rbp]
	mov rax, r9
	or rax, r14
	je 217f
	jmp 218f
217:
	mov r8, rbx
218:
	mov rdi, r8
	mov rsi, rbx
	cmp r9, 0
	je 219f
	mov rax, r14
	add rax, 1
	mul r13
	mov r10, rax
	cmp r14, 3
	je 221f
	jmp 222f
221:
	mov r10, 0
222:
	jmp 220f
219:
	mov r10, 0
220:
	cmp r9, 0
	je 223f
	mov rax, r12
	sub rax, r13
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
	jmp 224f
223:
	mov rax, r13
	mul r14
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
224:
	mov r8, r15
	sub r8, 1
	sbb r9, r9
	add rcx, r9
	mov rax, rdi
	xor rax, rsi
	sub rax, 1
	sbb rax, rax
	mov r8, rcx
	xor rdx, rcx
	and rdx, rax
	xor r8, rdx
	mov r9, rdi
	mov rdi, r11
	mov rsi, r8
	mov eax, edi
	mul rax
	shr rax, 32
	mul rsi
	shr rax, 32
	mov rcx, rsi
	sub rcx, 1
	sub rcx, rax
	mov rax, rcx
	mov rdi, rax
	add rdi, r10
	mov rsi, r12
	mov r10, rdi
	sub rdi, rsi
	sbb rax, rax
	xor r10, rdi
	and r10, rax
	xor rdi, r10
	mov r8, QWORD PTR [rbp+232]
	mov rsi, rdi
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 225f
	mov rdi, rcx
	jmp 226f
225:
	mov rdi, r12
226:
	sub rdi, 1
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r10, rax
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r11, rax
	mov rcx, rsi
	mov rax, r9
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r11
	mov QWORD PTR [rbp+16], r10
	mov rcx, QWORD PTR [rbp+248]
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress_avx512}
	mov rdi, QWORD PTR [rbp+16]
	mov rsi, QWORD PTR [rbp+248]
	add rsi, 4096
	mov r9, QWORD PTR [rbp]
	cmp r9, 0
	je 227f
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	jmp 228f
227:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	mov QWORD PTR [rdi+1016], rax
228:
	add r15, 1
	cmp r15, r13
	jb 210b
29:
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 25b
	add r14, 1
	cmp r14, 4
	jb 24b
	mov rax, QWORD PTR [rbp]
	add rax, 1
	mov QWORD PTR [rbp], rax
	cmp rax, QWORD PTR [rbp+72]
	jb 23b
	mov rdi, QWORD PTR [rbp+232]
	mov rbx, 0
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
229:
	mov r8, QWORD PTR [rbp+232]
	mov rax, rbx
	mov rcx, r12
	sub rcx, 1
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r8
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 229b
	mov rdi, QWORD PTR [rbp+232]
	mov rsi, 1024
	mov rdx, QWORD PTR [rbp+256]
	mov rcx, QWORD PTR [rbp+264]
	mov r8, QWORD PTR [rbp+248]
	call {vg_argon2_hprime_avx2}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop r15
	pop r14
	pop r13
	pop r12
	pop rbp
	pop rbx
	ret
	.p2align 6

vg_argon2_blake2b_avx2:
	push rbx
	push rbp
	push r12
	push r13
	push r14
	push r15
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+264], rax
	mov rbp, rsp
	mov edi, edi
	mov r9d, r9d
	mov QWORD PTR [rbp+72], r9
	mov QWORD PTR [rbp+80], r8
	mov QWORD PTR [rbp+88], rcx
	mov QWORD PTR [rbp+96], rdx
	mov QWORD PTR [rbp+104], rsi
	mov QWORD PTR [rbp+112], rdi
	mov rbx, QWORD PTR [rbp+248]
	mov rax, QWORD PTR [rbp+176]
	mov eax, eax
	mov QWORD PTR [rbp+176], rax
	mov rax, QWORD PTR [rbp+184]
	mov eax, eax
	mov QWORD PTR [rbp+184], rax
	mov rax, QWORD PTR [rbp+192]
	mov eax, eax
	mov QWORD PTR [rbp+192], rax
	mov rdi, QWORD PTR [rbp+176]
	mov rsi, QWORD PTR [rbp+184]
	add rsi, rsi
	add rsi, rsi
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r13, r9
	add r13, r13
	add r13, r13
	mov esi, 64
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 832
	mov ecx, 0
	call {vg_blake2b_init}
	mov rax, QWORD PTR [rbp+184]
	mov DWORD PTR [rbx+768], eax
	mov rax, QWORD PTR [rbp+264]
	mov DWORD PTR [rbx+772], eax
	mov rax, QWORD PTR [rbp+176]
	mov DWORD PTR [rbx+776], eax
	mov rax, QWORD PTR [rbp+72]
	mov DWORD PTR [rbx+780], eax
	mov eax, 19
	mov DWORD PTR [rbx+784], eax
	mov rax, QWORD PTR [rbp+112]
	mov DWORD PTR [rbx+788], eax
	mov esi, 0
	mov rdx, rbx
	add rdx, 768
	mov ecx, 24
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	mov r12d, 24
	mov r14, QWORD PTR [rbp+96]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+104]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, r14
	mov r14, QWORD PTR [rbp+80]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+88]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, r14
	mov r14, QWORD PTR [rbp+208]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+200]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, r14
	mov r14, QWORD PTR [rbp+224]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+216]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx2}
	add r12, r14
	mov rsi, r12
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 768
	mov rcx, rbx
	add rcx, 192
	call {vg_blake2b_finalize_scratch_avx2}
	mov r14, rbp
	mov eax, 64
	mov rdx, rbx
	add rdx, 768
20:
	movzx ecx, BYTE PTR [rdx]
	mov BYTE PTR [r14], cl
	add rdx, 1
	add r14, 1
	sub rax, 1
	jne 20b
	mov r14, QWORD PTR [rbp+232]
	mov rax, QWORD PTR [rbp+240]
	mov ecx, 0
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
21:
	mov QWORD PTR [r14], rcx
	add r14, 8
	sub rax, 1
	jne 21b
	mov r14, QWORD PTR [rbp+232]
	mov r12d, 0
	mov r15, QWORD PTR [rbp+184]
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
22:
	mov eax, 0
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime_avx2}
	add r14, 1024
	mov eax, 1
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime_avx2}
	add r14, r13
	sub r14, 1024
	add r12, 1
	sub r15, 1
	jne 22b
	mov r12, r13
	shr r12, 10
	shr r13, 12
	mov rax, 0
	mov QWORD PTR [rbp], rax
	mov rbx, 0
	mov r14, 0
23:
	mov r14, 0
24:
	mov rbx, 0
25:
	mov rax, 0
	mov QWORD PTR [rbp+8], rax
	mov rcx, QWORD PTR [rbp]
	or rcx, r14
	cmp rcx, 0
	je 26f
	mov r15, 0
	jmp 27f
26:
	mov r15, 2
27:
	cmp r15, r13
	jb 28f
	jmp 29f
28:
210:
	mov rax, QWORD PTR [rbp+112]
	mov r10, rax
	xor r10, 1
	cmp r10, 1
	sbb r10, r10
	mov r8, rax
	xor r8, 2
	cmp r8, 1
	sbb r8, r8
	mov r9, QWORD PTR [rbp]
	cmp r9, 1
	sbb r9, r9
	cmp r14, 2
	sbb r11, r11
	and r8, r9
	and r8, r11
	or r10, r8
	and r10, 1
	cmp r10, 0
	je 211f
	mov rax, r15
	shr rax, 7
	add rax, 1
	cmp rax, QWORD PTR [rbp+8]
	je 213f
	mov QWORD PTR [rbp+8], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 7168
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, QWORD PTR [rbp]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], r14
	mov rax, QWORD PTR [rbp+240]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rbp+72]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rbp+112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rbp+8]
	mov QWORD PTR [rdi+48], rax
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 5120
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress}
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 4096
	mov rdx, rcx
	add rdx, 6144
	call {vg_argon2_compress}
	jmp 214f
213:
214:
	mov rcx, QWORD PTR [rbp+248]
	mov rax, r15
	and rax, 127
	mov rdi, QWORD PTR [rcx+rax*8+6144]
	jmp 212f
211:
	mov r8, QWORD PTR [rbp+232]
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 215f
	mov rdi, rcx
	jmp 216f
215:
	mov rdi, r12
216:
	sub rdi, 1
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rdi, QWORD PTR [rax]
212:
	mov rsi, QWORD PTR [rbp+184]
	mov r11, rdi
	shr rdi, 32
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r9, QWORD PTR [rbp]
	mov rax, r9
	or rax, r14
	je 217f
	jmp 218f
217:
	mov r8, rbx
218:
	mov rdi, r8
	mov rsi, rbx
	cmp r9, 0
	je 219f
	mov rax, r14
	add rax, 1
	mul r13
	mov r10, rax
	cmp r14, 3
	je 221f
	jmp 222f
221:
	mov r10, 0
222:
	jmp 220f
219:
	mov r10, 0
220:
	cmp r9, 0
	je 223f
	mov rax, r12
	sub rax, r13
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
	jmp 224f
223:
	mov rax, r13
	mul r14
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
224:
	mov r8, r15
	sub r8, 1
	sbb r9, r9
	add rcx, r9
	mov rax, rdi
	xor rax, rsi
	sub rax, 1
	sbb rax, rax
	mov r8, rcx
	xor rdx, rcx
	and rdx, rax
	xor r8, rdx
	mov r9, rdi
	mov rdi, r11
	mov rsi, r8
	mov eax, edi
	mul rax
	shr rax, 32
	mul rsi
	shr rax, 32
	mov rcx, rsi
	sub rcx, 1
	sub rcx, rax
	mov rax, rcx
	mov rdi, rax
	add rdi, r10
	mov rsi, r12
	mov r10, rdi
	sub rdi, rsi
	sbb rax, rax
	xor r10, rdi
	and r10, rax
	xor rdi, r10
	mov r8, QWORD PTR [rbp+232]
	mov rsi, rdi
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 225f
	mov rdi, rcx
	jmp 226f
225:
	mov rdi, r12
226:
	sub rdi, 1
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r10, rax
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r11, rax
	mov rcx, rsi
	mov rax, r9
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r11
	mov QWORD PTR [rbp+16], r10
	mov rcx, QWORD PTR [rbp+248]
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress}
	mov rdi, QWORD PTR [rbp+16]
	mov rsi, QWORD PTR [rbp+248]
	add rsi, 4096
	mov r9, QWORD PTR [rbp]
	cmp r9, 0
	je 227f
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	jmp 228f
227:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	mov QWORD PTR [rdi+1016], rax
228:
	add r15, 1
	cmp r15, r13
	jb 210b
29:
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 25b
	add r14, 1
	cmp r14, 4
	jb 24b
	mov rax, QWORD PTR [rbp]
	add rax, 1
	mov QWORD PTR [rbp], rax
	cmp rax, QWORD PTR [rbp+72]
	jb 23b
	mov rdi, QWORD PTR [rbp+232]
	mov rbx, 0
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
229:
	mov r8, QWORD PTR [rbp+232]
	mov rax, rbx
	mov rcx, r12
	sub rcx, 1
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r8
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 229b
	mov rdi, QWORD PTR [rbp+232]
	mov rsi, 1024
	mov rdx, QWORD PTR [rbp+256]
	mov rcx, QWORD PTR [rbp+264]
	mov r8, QWORD PTR [rbp+248]
	call {vg_argon2_hprime_avx2}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop r15
	pop r14
	pop r13
	pop r12
	pop rbp
	pop rbx
	ret
	.p2align 6

vg_argon2_blake2b_avx512_g_avx2:
	push rbx
	push rbp
	push r12
	push r13
	push r14
	push r15
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+264], rax
	mov rbp, rsp
	mov edi, edi
	mov r9d, r9d
	mov QWORD PTR [rbp+72], r9
	mov QWORD PTR [rbp+80], r8
	mov QWORD PTR [rbp+88], rcx
	mov QWORD PTR [rbp+96], rdx
	mov QWORD PTR [rbp+104], rsi
	mov QWORD PTR [rbp+112], rdi
	mov rbx, QWORD PTR [rbp+248]
	mov rax, QWORD PTR [rbp+176]
	mov eax, eax
	mov QWORD PTR [rbp+176], rax
	mov rax, QWORD PTR [rbp+184]
	mov eax, eax
	mov QWORD PTR [rbp+184], rax
	mov rax, QWORD PTR [rbp+192]
	mov eax, eax
	mov QWORD PTR [rbp+192], rax
	mov rdi, QWORD PTR [rbp+176]
	mov rsi, QWORD PTR [rbp+184]
	add rsi, rsi
	add rsi, rsi
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r13, r9
	add r13, r13
	add r13, r13
	mov esi, 64
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 832
	mov ecx, 0
	call {vg_blake2b_init}
	mov rax, QWORD PTR [rbp+184]
	mov DWORD PTR [rbx+768], eax
	mov rax, QWORD PTR [rbp+264]
	mov DWORD PTR [rbx+772], eax
	mov rax, QWORD PTR [rbp+176]
	mov DWORD PTR [rbx+776], eax
	mov rax, QWORD PTR [rbp+72]
	mov DWORD PTR [rbx+780], eax
	mov eax, 19
	mov DWORD PTR [rbx+784], eax
	mov rax, QWORD PTR [rbp+112]
	mov DWORD PTR [rbx+788], eax
	mov esi, 0
	mov rdx, rbx
	add rdx, 768
	mov ecx, 24
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	mov r12d, 24
	mov r14, QWORD PTR [rbp+96]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+104]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, r14
	mov r14, QWORD PTR [rbp+80]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+88]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, r14
	mov r14, QWORD PTR [rbp+208]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+200]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, r14
	mov r14, QWORD PTR [rbp+224]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+216]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, r14
	mov rsi, r12
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 768
	mov rcx, rbx
	add rcx, 192
	call {vg_blake2b_finalize_scratch_avx512}
	mov r14, rbp
	mov eax, 64
	mov rdx, rbx
	add rdx, 768
20:
	movzx ecx, BYTE PTR [rdx]
	mov BYTE PTR [r14], cl
	add rdx, 1
	add r14, 1
	sub rax, 1
	jne 20b
	mov r14, QWORD PTR [rbp+232]
	mov rax, QWORD PTR [rbp+240]
	mov ecx, 0
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
21:
	mov QWORD PTR [r14], rcx
	add r14, 8
	sub rax, 1
	jne 21b
	mov r14, QWORD PTR [rbp+232]
	mov r12d, 0
	mov r15, QWORD PTR [rbp+184]
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
22:
	mov eax, 0
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime_avx512}
	add r14, 1024
	mov eax, 1
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime_avx512}
	add r14, r13
	sub r14, 1024
	add r12, 1
	sub r15, 1
	jne 22b
	mov r12, r13
	shr r12, 10
	shr r13, 12
	mov rax, 0
	mov QWORD PTR [rbp], rax
	mov rbx, 0
	mov r14, 0
23:
	mov r14, 0
24:
	mov rbx, 0
25:
	mov rax, 0
	mov QWORD PTR [rbp+8], rax
	mov rcx, QWORD PTR [rbp]
	or rcx, r14
	cmp rcx, 0
	je 26f
	mov r15, 0
	jmp 27f
26:
	mov r15, 2
27:
	cmp r15, r13
	jb 28f
	jmp 29f
28:
210:
	mov rax, QWORD PTR [rbp+112]
	mov r10, rax
	xor r10, 1
	cmp r10, 1
	sbb r10, r10
	mov r8, rax
	xor r8, 2
	cmp r8, 1
	sbb r8, r8
	mov r9, QWORD PTR [rbp]
	cmp r9, 1
	sbb r9, r9
	cmp r14, 2
	sbb r11, r11
	and r8, r9
	and r8, r11
	or r10, r8
	and r10, 1
	cmp r10, 0
	je 211f
	mov rax, r15
	shr rax, 7
	add rax, 1
	cmp rax, QWORD PTR [rbp+8]
	je 213f
	mov QWORD PTR [rbp+8], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 7168
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, QWORD PTR [rbp]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], r14
	mov rax, QWORD PTR [rbp+240]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rbp+72]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rbp+112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rbp+8]
	mov QWORD PTR [rdi+48], rax
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 5120
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress_avx2}
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 4096
	mov rdx, rcx
	add rdx, 6144
	call {vg_argon2_compress_avx2}
	jmp 214f
213:
214:
	mov rcx, QWORD PTR [rbp+248]
	mov rax, r15
	and rax, 127
	mov rdi, QWORD PTR [rcx+rax*8+6144]
	jmp 212f
211:
	mov r8, QWORD PTR [rbp+232]
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 215f
	mov rdi, rcx
	jmp 216f
215:
	mov rdi, r12
216:
	sub rdi, 1
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rdi, QWORD PTR [rax]
212:
	mov rsi, QWORD PTR [rbp+184]
	mov r11, rdi
	shr rdi, 32
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r9, QWORD PTR [rbp]
	mov rax, r9
	or rax, r14
	je 217f
	jmp 218f
217:
	mov r8, rbx
218:
	mov rdi, r8
	mov rsi, rbx
	cmp r9, 0
	je 219f
	mov rax, r14
	add rax, 1
	mul r13
	mov r10, rax
	cmp r14, 3
	je 221f
	jmp 222f
221:
	mov r10, 0
222:
	jmp 220f
219:
	mov r10, 0
220:
	cmp r9, 0
	je 223f
	mov rax, r12
	sub rax, r13
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
	jmp 224f
223:
	mov rax, r13
	mul r14
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
224:
	mov r8, r15
	sub r8, 1
	sbb r9, r9
	add rcx, r9
	mov rax, rdi
	xor rax, rsi
	sub rax, 1
	sbb rax, rax
	mov r8, rcx
	xor rdx, rcx
	and rdx, rax
	xor r8, rdx
	mov r9, rdi
	mov rdi, r11
	mov rsi, r8
	mov eax, edi
	mul rax
	shr rax, 32
	mul rsi
	shr rax, 32
	mov rcx, rsi
	sub rcx, 1
	sub rcx, rax
	mov rax, rcx
	mov rdi, rax
	add rdi, r10
	mov rsi, r12
	mov r10, rdi
	sub rdi, rsi
	sbb rax, rax
	xor r10, rdi
	and r10, rax
	xor rdi, r10
	mov r8, QWORD PTR [rbp+232]
	mov rsi, rdi
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 225f
	mov rdi, rcx
	jmp 226f
225:
	mov rdi, r12
226:
	sub rdi, 1
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r10, rax
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r11, rax
	mov rcx, rsi
	mov rax, r9
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r11
	mov QWORD PTR [rbp+16], r10
	mov rcx, QWORD PTR [rbp+248]
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress_avx2}
	mov rdi, QWORD PTR [rbp+16]
	mov rsi, QWORD PTR [rbp+248]
	add rsi, 4096
	mov r9, QWORD PTR [rbp]
	cmp r9, 0
	je 227f
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	jmp 228f
227:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	mov QWORD PTR [rdi+1016], rax
228:
	add r15, 1
	cmp r15, r13
	jb 210b
29:
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 25b
	add r14, 1
	cmp r14, 4
	jb 24b
	mov rax, QWORD PTR [rbp]
	add rax, 1
	mov QWORD PTR [rbp], rax
	cmp rax, QWORD PTR [rbp+72]
	jb 23b
	mov rdi, QWORD PTR [rbp+232]
	mov rbx, 0
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
229:
	mov r8, QWORD PTR [rbp+232]
	mov rax, rbx
	mov rcx, r12
	sub rcx, 1
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r8
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 229b
	mov rdi, QWORD PTR [rbp+232]
	mov rsi, 1024
	mov rdx, QWORD PTR [rbp+256]
	mov rcx, QWORD PTR [rbp+264]
	mov r8, QWORD PTR [rbp+248]
	call {vg_argon2_hprime_avx512}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop r15
	pop r14
	pop r13
	pop r12
	pop rbp
	pop rbx
	ret
	.p2align 6

vg_argon2_blake2b_avx512_g_avx512:
	push rbx
	push rbp
	push r12
	push r13
	push r14
	push r15
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+264], rax
	mov rbp, rsp
	mov edi, edi
	mov r9d, r9d
	mov QWORD PTR [rbp+72], r9
	mov QWORD PTR [rbp+80], r8
	mov QWORD PTR [rbp+88], rcx
	mov QWORD PTR [rbp+96], rdx
	mov QWORD PTR [rbp+104], rsi
	mov QWORD PTR [rbp+112], rdi
	mov rbx, QWORD PTR [rbp+248]
	mov rax, QWORD PTR [rbp+176]
	mov eax, eax
	mov QWORD PTR [rbp+176], rax
	mov rax, QWORD PTR [rbp+184]
	mov eax, eax
	mov QWORD PTR [rbp+184], rax
	mov rax, QWORD PTR [rbp+192]
	mov eax, eax
	mov QWORD PTR [rbp+192], rax
	mov rdi, QWORD PTR [rbp+176]
	mov rsi, QWORD PTR [rbp+184]
	add rsi, rsi
	add rsi, rsi
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r13, r9
	add r13, r13
	add r13, r13
	mov esi, 64
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 832
	mov ecx, 0
	call {vg_blake2b_init}
	mov rax, QWORD PTR [rbp+184]
	mov DWORD PTR [rbx+768], eax
	mov rax, QWORD PTR [rbp+264]
	mov DWORD PTR [rbx+772], eax
	mov rax, QWORD PTR [rbp+176]
	mov DWORD PTR [rbx+776], eax
	mov rax, QWORD PTR [rbp+72]
	mov DWORD PTR [rbx+780], eax
	mov eax, 19
	mov DWORD PTR [rbx+784], eax
	mov rax, QWORD PTR [rbp+112]
	mov DWORD PTR [rbx+788], eax
	mov esi, 0
	mov rdx, rbx
	add rdx, 768
	mov ecx, 24
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	mov r12d, 24
	mov r14, QWORD PTR [rbp+96]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+104]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, r14
	mov r14, QWORD PTR [rbp+80]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+88]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, r14
	mov r14, QWORD PTR [rbp+208]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+200]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, r14
	mov r14, QWORD PTR [rbp+224]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+216]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, r14
	mov rsi, r12
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 768
	mov rcx, rbx
	add rcx, 192
	call {vg_blake2b_finalize_scratch_avx512}
	mov r14, rbp
	mov eax, 64
	mov rdx, rbx
	add rdx, 768
20:
	movzx ecx, BYTE PTR [rdx]
	mov BYTE PTR [r14], cl
	add rdx, 1
	add r14, 1
	sub rax, 1
	jne 20b
	mov r14, QWORD PTR [rbp+232]
	mov rax, QWORD PTR [rbp+240]
	mov ecx, 0
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
21:
	mov QWORD PTR [r14], rcx
	add r14, 8
	sub rax, 1
	jne 21b
	mov r14, QWORD PTR [rbp+232]
	mov r12d, 0
	mov r15, QWORD PTR [rbp+184]
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
22:
	mov eax, 0
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime_avx512}
	add r14, 1024
	mov eax, 1
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime_avx512}
	add r14, r13
	sub r14, 1024
	add r12, 1
	sub r15, 1
	jne 22b
	mov r12, r13
	shr r12, 10
	shr r13, 12
	mov rax, 0
	mov QWORD PTR [rbp], rax
	mov rbx, 0
	mov r14, 0
23:
	mov r14, 0
24:
	mov rbx, 0
25:
	mov rax, 0
	mov QWORD PTR [rbp+8], rax
	mov rcx, QWORD PTR [rbp]
	or rcx, r14
	cmp rcx, 0
	je 26f
	mov r15, 0
	jmp 27f
26:
	mov r15, 2
27:
	cmp r15, r13
	jb 28f
	jmp 29f
28:
210:
	mov rax, QWORD PTR [rbp+112]
	mov r10, rax
	xor r10, 1
	cmp r10, 1
	sbb r10, r10
	mov r8, rax
	xor r8, 2
	cmp r8, 1
	sbb r8, r8
	mov r9, QWORD PTR [rbp]
	cmp r9, 1
	sbb r9, r9
	cmp r14, 2
	sbb r11, r11
	and r8, r9
	and r8, r11
	or r10, r8
	and r10, 1
	cmp r10, 0
	je 211f
	mov rax, r15
	shr rax, 7
	add rax, 1
	cmp rax, QWORD PTR [rbp+8]
	je 213f
	mov QWORD PTR [rbp+8], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 7168
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, QWORD PTR [rbp]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], r14
	mov rax, QWORD PTR [rbp+240]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rbp+72]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rbp+112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rbp+8]
	mov QWORD PTR [rdi+48], rax
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 5120
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress_avx512}
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 4096
	mov rdx, rcx
	add rdx, 6144
	call {vg_argon2_compress_avx512}
	jmp 214f
213:
214:
	mov rcx, QWORD PTR [rbp+248]
	mov rax, r15
	and rax, 127
	mov rdi, QWORD PTR [rcx+rax*8+6144]
	jmp 212f
211:
	mov r8, QWORD PTR [rbp+232]
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 215f
	mov rdi, rcx
	jmp 216f
215:
	mov rdi, r12
216:
	sub rdi, 1
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rdi, QWORD PTR [rax]
212:
	mov rsi, QWORD PTR [rbp+184]
	mov r11, rdi
	shr rdi, 32
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r9, QWORD PTR [rbp]
	mov rax, r9
	or rax, r14
	je 217f
	jmp 218f
217:
	mov r8, rbx
218:
	mov rdi, r8
	mov rsi, rbx
	cmp r9, 0
	je 219f
	mov rax, r14
	add rax, 1
	mul r13
	mov r10, rax
	cmp r14, 3
	je 221f
	jmp 222f
221:
	mov r10, 0
222:
	jmp 220f
219:
	mov r10, 0
220:
	cmp r9, 0
	je 223f
	mov rax, r12
	sub rax, r13
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
	jmp 224f
223:
	mov rax, r13
	mul r14
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
224:
	mov r8, r15
	sub r8, 1
	sbb r9, r9
	add rcx, r9
	mov rax, rdi
	xor rax, rsi
	sub rax, 1
	sbb rax, rax
	mov r8, rcx
	xor rdx, rcx
	and rdx, rax
	xor r8, rdx
	mov r9, rdi
	mov rdi, r11
	mov rsi, r8
	mov eax, edi
	mul rax
	shr rax, 32
	mul rsi
	shr rax, 32
	mov rcx, rsi
	sub rcx, 1
	sub rcx, rax
	mov rax, rcx
	mov rdi, rax
	add rdi, r10
	mov rsi, r12
	mov r10, rdi
	sub rdi, rsi
	sbb rax, rax
	xor r10, rdi
	and r10, rax
	xor rdi, r10
	mov r8, QWORD PTR [rbp+232]
	mov rsi, rdi
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 225f
	mov rdi, rcx
	jmp 226f
225:
	mov rdi, r12
226:
	sub rdi, 1
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r10, rax
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r11, rax
	mov rcx, rsi
	mov rax, r9
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r11
	mov QWORD PTR [rbp+16], r10
	mov rcx, QWORD PTR [rbp+248]
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress_avx512}
	mov rdi, QWORD PTR [rbp+16]
	mov rsi, QWORD PTR [rbp+248]
	add rsi, 4096
	mov r9, QWORD PTR [rbp]
	cmp r9, 0
	je 227f
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	jmp 228f
227:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	mov QWORD PTR [rdi+1016], rax
228:
	add r15, 1
	cmp r15, r13
	jb 210b
29:
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 25b
	add r14, 1
	cmp r14, 4
	jb 24b
	mov rax, QWORD PTR [rbp]
	add rax, 1
	mov QWORD PTR [rbp], rax
	cmp rax, QWORD PTR [rbp+72]
	jb 23b
	mov rdi, QWORD PTR [rbp+232]
	mov rbx, 0
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
229:
	mov r8, QWORD PTR [rbp+232]
	mov rax, rbx
	mov rcx, r12
	sub rcx, 1
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r8
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 229b
	mov rdi, QWORD PTR [rbp+232]
	mov rsi, 1024
	mov rdx, QWORD PTR [rbp+256]
	mov rcx, QWORD PTR [rbp+264]
	mov r8, QWORD PTR [rbp+248]
	call {vg_argon2_hprime_avx512}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop r15
	pop r14
	pop r13
	pop r12
	pop rbp
	pop rbx
	ret
	.p2align 6

vg_argon2_blake2b_avx512:
	push rbx
	push rbp
	push r12
	push r13
	push r14
	push r15
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+264], rax
	mov rbp, rsp
	mov edi, edi
	mov r9d, r9d
	mov QWORD PTR [rbp+72], r9
	mov QWORD PTR [rbp+80], r8
	mov QWORD PTR [rbp+88], rcx
	mov QWORD PTR [rbp+96], rdx
	mov QWORD PTR [rbp+104], rsi
	mov QWORD PTR [rbp+112], rdi
	mov rbx, QWORD PTR [rbp+248]
	mov rax, QWORD PTR [rbp+176]
	mov eax, eax
	mov QWORD PTR [rbp+176], rax
	mov rax, QWORD PTR [rbp+184]
	mov eax, eax
	mov QWORD PTR [rbp+184], rax
	mov rax, QWORD PTR [rbp+192]
	mov eax, eax
	mov QWORD PTR [rbp+192], rax
	mov rdi, QWORD PTR [rbp+176]
	mov rsi, QWORD PTR [rbp+184]
	add rsi, rsi
	add rsi, rsi
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r13, r9
	add r13, r13
	add r13, r13
	mov esi, 64
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 832
	mov ecx, 0
	call {vg_blake2b_init}
	mov rax, QWORD PTR [rbp+184]
	mov DWORD PTR [rbx+768], eax
	mov rax, QWORD PTR [rbp+264]
	mov DWORD PTR [rbx+772], eax
	mov rax, QWORD PTR [rbp+176]
	mov DWORD PTR [rbx+776], eax
	mov rax, QWORD PTR [rbp+72]
	mov DWORD PTR [rbx+780], eax
	mov eax, 19
	mov DWORD PTR [rbx+784], eax
	mov rax, QWORD PTR [rbp+112]
	mov DWORD PTR [rbx+788], eax
	mov esi, 0
	mov rdx, rbx
	add rdx, 768
	mov ecx, 24
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	mov r12d, 24
	mov r14, QWORD PTR [rbp+96]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+104]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, r14
	mov r14, QWORD PTR [rbp+80]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+88]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, r14
	mov r14, QWORD PTR [rbp+208]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+200]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, r14
	mov r14, QWORD PTR [rbp+224]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+216]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch_avx512}
	add r12, r14
	mov rsi, r12
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 768
	mov rcx, rbx
	add rcx, 192
	call {vg_blake2b_finalize_scratch_avx512}
	mov r14, rbp
	mov eax, 64
	mov rdx, rbx
	add rdx, 768
20:
	movzx ecx, BYTE PTR [rdx]
	mov BYTE PTR [r14], cl
	add rdx, 1
	add r14, 1
	sub rax, 1
	jne 20b
	mov r14, QWORD PTR [rbp+232]
	mov rax, QWORD PTR [rbp+240]
	mov ecx, 0
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
21:
	mov QWORD PTR [r14], rcx
	add r14, 8
	sub rax, 1
	jne 21b
	mov r14, QWORD PTR [rbp+232]
	mov r12d, 0
	mov r15, QWORD PTR [rbp+184]
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
22:
	mov eax, 0
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime_avx512}
	add r14, 1024
	mov eax, 1
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime_avx512}
	add r14, r13
	sub r14, 1024
	add r12, 1
	sub r15, 1
	jne 22b
	mov r12, r13
	shr r12, 10
	shr r13, 12
	mov rax, 0
	mov QWORD PTR [rbp], rax
	mov rbx, 0
	mov r14, 0
23:
	mov r14, 0
24:
	mov rbx, 0
25:
	mov rax, 0
	mov QWORD PTR [rbp+8], rax
	mov rcx, QWORD PTR [rbp]
	or rcx, r14
	cmp rcx, 0
	je 26f
	mov r15, 0
	jmp 27f
26:
	mov r15, 2
27:
	cmp r15, r13
	jb 28f
	jmp 29f
28:
210:
	mov rax, QWORD PTR [rbp+112]
	mov r10, rax
	xor r10, 1
	cmp r10, 1
	sbb r10, r10
	mov r8, rax
	xor r8, 2
	cmp r8, 1
	sbb r8, r8
	mov r9, QWORD PTR [rbp]
	cmp r9, 1
	sbb r9, r9
	cmp r14, 2
	sbb r11, r11
	and r8, r9
	and r8, r11
	or r10, r8
	and r10, 1
	cmp r10, 0
	je 211f
	mov rax, r15
	shr rax, 7
	add rax, 1
	cmp rax, QWORD PTR [rbp+8]
	je 213f
	mov QWORD PTR [rbp+8], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 7168
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, QWORD PTR [rbp]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], r14
	mov rax, QWORD PTR [rbp+240]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rbp+72]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rbp+112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rbp+8]
	mov QWORD PTR [rdi+48], rax
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 5120
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress}
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 4096
	mov rdx, rcx
	add rdx, 6144
	call {vg_argon2_compress}
	jmp 214f
213:
214:
	mov rcx, QWORD PTR [rbp+248]
	mov rax, r15
	and rax, 127
	mov rdi, QWORD PTR [rcx+rax*8+6144]
	jmp 212f
211:
	mov r8, QWORD PTR [rbp+232]
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 215f
	mov rdi, rcx
	jmp 216f
215:
	mov rdi, r12
216:
	sub rdi, 1
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rdi, QWORD PTR [rax]
212:
	mov rsi, QWORD PTR [rbp+184]
	mov r11, rdi
	shr rdi, 32
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r9, QWORD PTR [rbp]
	mov rax, r9
	or rax, r14
	je 217f
	jmp 218f
217:
	mov r8, rbx
218:
	mov rdi, r8
	mov rsi, rbx
	cmp r9, 0
	je 219f
	mov rax, r14
	add rax, 1
	mul r13
	mov r10, rax
	cmp r14, 3
	je 221f
	jmp 222f
221:
	mov r10, 0
222:
	jmp 220f
219:
	mov r10, 0
220:
	cmp r9, 0
	je 223f
	mov rax, r12
	sub rax, r13
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
	jmp 224f
223:
	mov rax, r13
	mul r14
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
224:
	mov r8, r15
	sub r8, 1
	sbb r9, r9
	add rcx, r9
	mov rax, rdi
	xor rax, rsi
	sub rax, 1
	sbb rax, rax
	mov r8, rcx
	xor rdx, rcx
	and rdx, rax
	xor r8, rdx
	mov r9, rdi
	mov rdi, r11
	mov rsi, r8
	mov eax, edi
	mul rax
	shr rax, 32
	mul rsi
	shr rax, 32
	mov rcx, rsi
	sub rcx, 1
	sub rcx, rax
	mov rax, rcx
	mov rdi, rax
	add rdi, r10
	mov rsi, r12
	mov r10, rdi
	sub rdi, rsi
	sbb rax, rax
	xor r10, rdi
	and r10, rax
	xor rdi, r10
	mov r8, QWORD PTR [rbp+232]
	mov rsi, rdi
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 225f
	mov rdi, rcx
	jmp 226f
225:
	mov rdi, r12
226:
	sub rdi, 1
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r10, rax
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r11, rax
	mov rcx, rsi
	mov rax, r9
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r11
	mov QWORD PTR [rbp+16], r10
	mov rcx, QWORD PTR [rbp+248]
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress}
	mov rdi, QWORD PTR [rbp+16]
	mov rsi, QWORD PTR [rbp+248]
	add rsi, 4096
	mov r9, QWORD PTR [rbp]
	cmp r9, 0
	je 227f
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	jmp 228f
227:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	mov QWORD PTR [rdi+1016], rax
228:
	add r15, 1
	cmp r15, r13
	jb 210b
29:
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 25b
	add r14, 1
	cmp r14, 4
	jb 24b
	mov rax, QWORD PTR [rbp]
	add rax, 1
	mov QWORD PTR [rbp], rax
	cmp rax, QWORD PTR [rbp+72]
	jb 23b
	mov rdi, QWORD PTR [rbp+232]
	mov rbx, 0
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
229:
	mov r8, QWORD PTR [rbp+232]
	mov rax, rbx
	mov rcx, r12
	sub rcx, 1
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r8
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 229b
	mov rdi, QWORD PTR [rbp+232]
	mov rsi, 1024
	mov rdx, QWORD PTR [rbp+256]
	mov rcx, QWORD PTR [rbp+264]
	mov r8, QWORD PTR [rbp+248]
	call {vg_argon2_hprime_avx512}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop r15
	pop r14
	pop r13
	pop r12
	pop rbp
	pop rbx
	ret
	.p2align 6

vg_argon2_g_avx2:
	push rbx
	push rbp
	push r12
	push r13
	push r14
	push r15
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+264], rax
	mov rbp, rsp
	mov edi, edi
	mov r9d, r9d
	mov QWORD PTR [rbp+72], r9
	mov QWORD PTR [rbp+80], r8
	mov QWORD PTR [rbp+88], rcx
	mov QWORD PTR [rbp+96], rdx
	mov QWORD PTR [rbp+104], rsi
	mov QWORD PTR [rbp+112], rdi
	mov rbx, QWORD PTR [rbp+248]
	mov rax, QWORD PTR [rbp+176]
	mov eax, eax
	mov QWORD PTR [rbp+176], rax
	mov rax, QWORD PTR [rbp+184]
	mov eax, eax
	mov QWORD PTR [rbp+184], rax
	mov rax, QWORD PTR [rbp+192]
	mov eax, eax
	mov QWORD PTR [rbp+192], rax
	mov rdi, QWORD PTR [rbp+176]
	mov rsi, QWORD PTR [rbp+184]
	add rsi, rsi
	add rsi, rsi
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r13, r9
	add r13, r13
	add r13, r13
	mov esi, 64
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 832
	mov ecx, 0
	call {vg_blake2b_init}
	mov rax, QWORD PTR [rbp+184]
	mov DWORD PTR [rbx+768], eax
	mov rax, QWORD PTR [rbp+264]
	mov DWORD PTR [rbx+772], eax
	mov rax, QWORD PTR [rbp+176]
	mov DWORD PTR [rbx+776], eax
	mov rax, QWORD PTR [rbp+72]
	mov DWORD PTR [rbx+780], eax
	mov eax, 19
	mov DWORD PTR [rbx+784], eax
	mov rax, QWORD PTR [rbp+112]
	mov DWORD PTR [rbx+788], eax
	mov esi, 0
	mov rdx, rbx
	add rdx, 768
	mov ecx, 24
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	mov r12d, 24
	mov r14, QWORD PTR [rbp+96]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+104]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, r14
	mov r14, QWORD PTR [rbp+80]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+88]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, r14
	mov r14, QWORD PTR [rbp+208]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+200]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, r14
	mov r14, QWORD PTR [rbp+224]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+216]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, r14
	mov rsi, r12
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 768
	mov rcx, rbx
	add rcx, 192
	call {vg_blake2b_finalize_scratch}
	mov r14, rbp
	mov eax, 64
	mov rdx, rbx
	add rdx, 768
20:
	movzx ecx, BYTE PTR [rdx]
	mov BYTE PTR [r14], cl
	add rdx, 1
	add r14, 1
	sub rax, 1
	jne 20b
	mov r14, QWORD PTR [rbp+232]
	mov rax, QWORD PTR [rbp+240]
	mov ecx, 0
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
21:
	mov QWORD PTR [r14], rcx
	add r14, 8
	sub rax, 1
	jne 21b
	mov r14, QWORD PTR [rbp+232]
	mov r12d, 0
	mov r15, QWORD PTR [rbp+184]
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
22:
	mov eax, 0
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime}
	add r14, 1024
	mov eax, 1
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime}
	add r14, r13
	sub r14, 1024
	add r12, 1
	sub r15, 1
	jne 22b
	mov r12, r13
	shr r12, 10
	shr r13, 12
	mov rax, 0
	mov QWORD PTR [rbp], rax
	mov rbx, 0
	mov r14, 0
23:
	mov r14, 0
24:
	mov rbx, 0
25:
	mov rax, 0
	mov QWORD PTR [rbp+8], rax
	mov rcx, QWORD PTR [rbp]
	or rcx, r14
	cmp rcx, 0
	je 26f
	mov r15, 0
	jmp 27f
26:
	mov r15, 2
27:
	cmp r15, r13
	jb 28f
	jmp 29f
28:
210:
	mov rax, QWORD PTR [rbp+112]
	mov r10, rax
	xor r10, 1
	cmp r10, 1
	sbb r10, r10
	mov r8, rax
	xor r8, 2
	cmp r8, 1
	sbb r8, r8
	mov r9, QWORD PTR [rbp]
	cmp r9, 1
	sbb r9, r9
	cmp r14, 2
	sbb r11, r11
	and r8, r9
	and r8, r11
	or r10, r8
	and r10, 1
	cmp r10, 0
	je 211f
	mov rax, r15
	shr rax, 7
	add rax, 1
	cmp rax, QWORD PTR [rbp+8]
	je 213f
	mov QWORD PTR [rbp+8], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 7168
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, QWORD PTR [rbp]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], r14
	mov rax, QWORD PTR [rbp+240]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rbp+72]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rbp+112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rbp+8]
	mov QWORD PTR [rdi+48], rax
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 5120
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress_avx2}
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 4096
	mov rdx, rcx
	add rdx, 6144
	call {vg_argon2_compress_avx2}
	jmp 214f
213:
214:
	mov rcx, QWORD PTR [rbp+248]
	mov rax, r15
	and rax, 127
	mov rdi, QWORD PTR [rcx+rax*8+6144]
	jmp 212f
211:
	mov r8, QWORD PTR [rbp+232]
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 215f
	mov rdi, rcx
	jmp 216f
215:
	mov rdi, r12
216:
	sub rdi, 1
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rdi, QWORD PTR [rax]
212:
	mov rsi, QWORD PTR [rbp+184]
	mov r11, rdi
	shr rdi, 32
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r9, QWORD PTR [rbp]
	mov rax, r9
	or rax, r14
	je 217f
	jmp 218f
217:
	mov r8, rbx
218:
	mov rdi, r8
	mov rsi, rbx
	cmp r9, 0
	je 219f
	mov rax, r14
	add rax, 1
	mul r13
	mov r10, rax
	cmp r14, 3
	je 221f
	jmp 222f
221:
	mov r10, 0
222:
	jmp 220f
219:
	mov r10, 0
220:
	cmp r9, 0
	je 223f
	mov rax, r12
	sub rax, r13
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
	jmp 224f
223:
	mov rax, r13
	mul r14
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
224:
	mov r8, r15
	sub r8, 1
	sbb r9, r9
	add rcx, r9
	mov rax, rdi
	xor rax, rsi
	sub rax, 1
	sbb rax, rax
	mov r8, rcx
	xor rdx, rcx
	and rdx, rax
	xor r8, rdx
	mov r9, rdi
	mov rdi, r11
	mov rsi, r8
	mov eax, edi
	mul rax
	shr rax, 32
	mul rsi
	shr rax, 32
	mov rcx, rsi
	sub rcx, 1
	sub rcx, rax
	mov rax, rcx
	mov rdi, rax
	add rdi, r10
	mov rsi, r12
	mov r10, rdi
	sub rdi, rsi
	sbb rax, rax
	xor r10, rdi
	and r10, rax
	xor rdi, r10
	mov r8, QWORD PTR [rbp+232]
	mov rsi, rdi
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 225f
	mov rdi, rcx
	jmp 226f
225:
	mov rdi, r12
226:
	sub rdi, 1
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r10, rax
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r11, rax
	mov rcx, rsi
	mov rax, r9
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r11
	mov QWORD PTR [rbp+16], r10
	mov rcx, QWORD PTR [rbp+248]
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress_avx2}
	mov rdi, QWORD PTR [rbp+16]
	mov rsi, QWORD PTR [rbp+248]
	add rsi, 4096
	mov r9, QWORD PTR [rbp]
	cmp r9, 0
	je 227f
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	jmp 228f
227:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	mov QWORD PTR [rdi+1016], rax
228:
	add r15, 1
	cmp r15, r13
	jb 210b
29:
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 25b
	add r14, 1
	cmp r14, 4
	jb 24b
	mov rax, QWORD PTR [rbp]
	add rax, 1
	mov QWORD PTR [rbp], rax
	cmp rax, QWORD PTR [rbp+72]
	jb 23b
	mov rdi, QWORD PTR [rbp+232]
	mov rbx, 0
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
229:
	mov r8, QWORD PTR [rbp+232]
	mov rax, rbx
	mov rcx, r12
	sub rcx, 1
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r8
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 229b
	mov rdi, QWORD PTR [rbp+232]
	mov rsi, 1024
	mov rdx, QWORD PTR [rbp+256]
	mov rcx, QWORD PTR [rbp+264]
	mov r8, QWORD PTR [rbp+248]
	call {vg_argon2_hprime}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop r15
	pop r14
	pop r13
	pop r12
	pop rbp
	pop rbx
	ret
	.p2align 6

vg_argon2_g_avx512:
	push rbx
	push rbp
	push r12
	push r13
	push r14
	push r15
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+264], rax
	mov rbp, rsp
	mov edi, edi
	mov r9d, r9d
	mov QWORD PTR [rbp+72], r9
	mov QWORD PTR [rbp+80], r8
	mov QWORD PTR [rbp+88], rcx
	mov QWORD PTR [rbp+96], rdx
	mov QWORD PTR [rbp+104], rsi
	mov QWORD PTR [rbp+112], rdi
	mov rbx, QWORD PTR [rbp+248]
	mov rax, QWORD PTR [rbp+176]
	mov eax, eax
	mov QWORD PTR [rbp+176], rax
	mov rax, QWORD PTR [rbp+184]
	mov eax, eax
	mov QWORD PTR [rbp+184], rax
	mov rax, QWORD PTR [rbp+192]
	mov eax, eax
	mov QWORD PTR [rbp+192], rax
	mov rdi, QWORD PTR [rbp+176]
	mov rsi, QWORD PTR [rbp+184]
	add rsi, rsi
	add rsi, rsi
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r13, r9
	add r13, r13
	add r13, r13
	mov esi, 64
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 832
	mov ecx, 0
	call {vg_blake2b_init}
	mov rax, QWORD PTR [rbp+184]
	mov DWORD PTR [rbx+768], eax
	mov rax, QWORD PTR [rbp+264]
	mov DWORD PTR [rbx+772], eax
	mov rax, QWORD PTR [rbp+176]
	mov DWORD PTR [rbx+776], eax
	mov rax, QWORD PTR [rbp+72]
	mov DWORD PTR [rbx+780], eax
	mov eax, 19
	mov DWORD PTR [rbx+784], eax
	mov rax, QWORD PTR [rbp+112]
	mov DWORD PTR [rbx+788], eax
	mov esi, 0
	mov rdx, rbx
	add rdx, 768
	mov ecx, 24
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	mov r12d, 24
	mov r14, QWORD PTR [rbp+96]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+104]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, r14
	mov r14, QWORD PTR [rbp+80]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+88]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, r14
	mov r14, QWORD PTR [rbp+208]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+200]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, r14
	mov r14, QWORD PTR [rbp+224]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+216]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, r14
	mov rsi, r12
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 768
	mov rcx, rbx
	add rcx, 192
	call {vg_blake2b_finalize_scratch}
	mov r14, rbp
	mov eax, 64
	mov rdx, rbx
	add rdx, 768
20:
	movzx ecx, BYTE PTR [rdx]
	mov BYTE PTR [r14], cl
	add rdx, 1
	add r14, 1
	sub rax, 1
	jne 20b
	mov r14, QWORD PTR [rbp+232]
	mov rax, QWORD PTR [rbp+240]
	mov ecx, 0
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
21:
	mov QWORD PTR [r14], rcx
	add r14, 8
	sub rax, 1
	jne 21b
	mov r14, QWORD PTR [rbp+232]
	mov r12d, 0
	mov r15, QWORD PTR [rbp+184]
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
22:
	mov eax, 0
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime}
	add r14, 1024
	mov eax, 1
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime}
	add r14, r13
	sub r14, 1024
	add r12, 1
	sub r15, 1
	jne 22b
	mov r12, r13
	shr r12, 10
	shr r13, 12
	mov rax, 0
	mov QWORD PTR [rbp], rax
	mov rbx, 0
	mov r14, 0
23:
	mov r14, 0
24:
	mov rbx, 0
25:
	mov rax, 0
	mov QWORD PTR [rbp+8], rax
	mov rcx, QWORD PTR [rbp]
	or rcx, r14
	cmp rcx, 0
	je 26f
	mov r15, 0
	jmp 27f
26:
	mov r15, 2
27:
	cmp r15, r13
	jb 28f
	jmp 29f
28:
210:
	mov rax, QWORD PTR [rbp+112]
	mov r10, rax
	xor r10, 1
	cmp r10, 1
	sbb r10, r10
	mov r8, rax
	xor r8, 2
	cmp r8, 1
	sbb r8, r8
	mov r9, QWORD PTR [rbp]
	cmp r9, 1
	sbb r9, r9
	cmp r14, 2
	sbb r11, r11
	and r8, r9
	and r8, r11
	or r10, r8
	and r10, 1
	cmp r10, 0
	je 211f
	mov rax, r15
	shr rax, 7
	add rax, 1
	cmp rax, QWORD PTR [rbp+8]
	je 213f
	mov QWORD PTR [rbp+8], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 7168
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, QWORD PTR [rbp]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], r14
	mov rax, QWORD PTR [rbp+240]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rbp+72]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rbp+112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rbp+8]
	mov QWORD PTR [rdi+48], rax
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 5120
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress_avx512}
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 4096
	mov rdx, rcx
	add rdx, 6144
	call {vg_argon2_compress_avx512}
	jmp 214f
213:
214:
	mov rcx, QWORD PTR [rbp+248]
	mov rax, r15
	and rax, 127
	mov rdi, QWORD PTR [rcx+rax*8+6144]
	jmp 212f
211:
	mov r8, QWORD PTR [rbp+232]
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 215f
	mov rdi, rcx
	jmp 216f
215:
	mov rdi, r12
216:
	sub rdi, 1
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rdi, QWORD PTR [rax]
212:
	mov rsi, QWORD PTR [rbp+184]
	mov r11, rdi
	shr rdi, 32
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r9, QWORD PTR [rbp]
	mov rax, r9
	or rax, r14
	je 217f
	jmp 218f
217:
	mov r8, rbx
218:
	mov rdi, r8
	mov rsi, rbx
	cmp r9, 0
	je 219f
	mov rax, r14
	add rax, 1
	mul r13
	mov r10, rax
	cmp r14, 3
	je 221f
	jmp 222f
221:
	mov r10, 0
222:
	jmp 220f
219:
	mov r10, 0
220:
	cmp r9, 0
	je 223f
	mov rax, r12
	sub rax, r13
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
	jmp 224f
223:
	mov rax, r13
	mul r14
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
224:
	mov r8, r15
	sub r8, 1
	sbb r9, r9
	add rcx, r9
	mov rax, rdi
	xor rax, rsi
	sub rax, 1
	sbb rax, rax
	mov r8, rcx
	xor rdx, rcx
	and rdx, rax
	xor r8, rdx
	mov r9, rdi
	mov rdi, r11
	mov rsi, r8
	mov eax, edi
	mul rax
	shr rax, 32
	mul rsi
	shr rax, 32
	mov rcx, rsi
	sub rcx, 1
	sub rcx, rax
	mov rax, rcx
	mov rdi, rax
	add rdi, r10
	mov rsi, r12
	mov r10, rdi
	sub rdi, rsi
	sbb rax, rax
	xor r10, rdi
	and r10, rax
	xor rdi, r10
	mov r8, QWORD PTR [rbp+232]
	mov rsi, rdi
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 225f
	mov rdi, rcx
	jmp 226f
225:
	mov rdi, r12
226:
	sub rdi, 1
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r10, rax
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r11, rax
	mov rcx, rsi
	mov rax, r9
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r11
	mov QWORD PTR [rbp+16], r10
	mov rcx, QWORD PTR [rbp+248]
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress_avx512}
	mov rdi, QWORD PTR [rbp+16]
	mov rsi, QWORD PTR [rbp+248]
	add rsi, 4096
	mov r9, QWORD PTR [rbp]
	cmp r9, 0
	je 227f
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	jmp 228f
227:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	mov QWORD PTR [rdi+1016], rax
228:
	add r15, 1
	cmp r15, r13
	jb 210b
29:
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 25b
	add r14, 1
	cmp r14, 4
	jb 24b
	mov rax, QWORD PTR [rbp]
	add rax, 1
	mov QWORD PTR [rbp], rax
	cmp rax, QWORD PTR [rbp+72]
	jb 23b
	mov rdi, QWORD PTR [rbp+232]
	mov rbx, 0
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
229:
	mov r8, QWORD PTR [rbp+232]
	mov rax, rbx
	mov rcx, r12
	sub rcx, 1
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r8
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 229b
	mov rdi, QWORD PTR [rbp+232]
	mov rsi, 1024
	mov rdx, QWORD PTR [rbp+256]
	mov rcx, QWORD PTR [rbp+264]
	mov r8, QWORD PTR [rbp+248]
	call {vg_argon2_hprime}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop r15
	pop r14
	pop r13
	pop r12
	pop rbp
	pop rbx
	ret
	.p2align 6

vg_argon2:
	push rbx
	push rbp
	push r12
	push r13
	push r14
	push r15
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+192], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+360]
	mov QWORD PTR [rsp+208], rax
	mov rax, QWORD PTR [rsp+368]
	mov QWORD PTR [rsp+216], rax
	mov rax, QWORD PTR [rsp+376]
	mov QWORD PTR [rsp+224], rax
	mov rax, QWORD PTR [rsp+384]
	mov QWORD PTR [rsp+232], rax
	mov rax, QWORD PTR [rsp+392]
	mov QWORD PTR [rsp+240], rax
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+248], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+256], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+264], rax
	mov rbp, rsp
	mov edi, edi
	mov r9d, r9d
	mov QWORD PTR [rbp+72], r9
	mov QWORD PTR [rbp+80], r8
	mov QWORD PTR [rbp+88], rcx
	mov QWORD PTR [rbp+96], rdx
	mov QWORD PTR [rbp+104], rsi
	mov QWORD PTR [rbp+112], rdi
	mov rbx, QWORD PTR [rbp+248]
	mov rax, QWORD PTR [rbp+176]
	mov eax, eax
	mov QWORD PTR [rbp+176], rax
	mov rax, QWORD PTR [rbp+184]
	mov eax, eax
	mov QWORD PTR [rbp+184], rax
	mov rax, QWORD PTR [rbp+192]
	mov eax, eax
	mov QWORD PTR [rbp+192], rax
	mov rdi, QWORD PTR [rbp+176]
	mov rsi, QWORD PTR [rbp+184]
	add rsi, rsi
	add rsi, rsi
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r13, r9
	add r13, r13
	add r13, r13
	mov esi, 64
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 832
	mov ecx, 0
	call {vg_blake2b_init}
	mov rax, QWORD PTR [rbp+184]
	mov DWORD PTR [rbx+768], eax
	mov rax, QWORD PTR [rbp+264]
	mov DWORD PTR [rbx+772], eax
	mov rax, QWORD PTR [rbp+176]
	mov DWORD PTR [rbx+776], eax
	mov rax, QWORD PTR [rbp+72]
	mov DWORD PTR [rbx+780], eax
	mov eax, 19
	mov DWORD PTR [rbx+784], eax
	mov rax, QWORD PTR [rbp+112]
	mov DWORD PTR [rbx+788], eax
	mov esi, 0
	mov rdx, rbx
	add rdx, 768
	mov ecx, 24
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	mov r12d, 24
	mov r14, QWORD PTR [rbp+96]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+104]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, r14
	mov r14, QWORD PTR [rbp+80]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+88]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, r14
	mov r14, QWORD PTR [rbp+208]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+200]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, r14
	mov r14, QWORD PTR [rbp+224]
	mov DWORD PTR [rbx+792], r14d
	mov rsi, r12
	mov rdx, rbx
	add rdx, 792
	mov ecx, 4
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, 4
	mov rsi, r12
	mov rdx, QWORD PTR [rbp+216]
	mov rcx, r14
	mov rdi, rbx
	mov r8, rbx
	add r8, 192
	call {vg_blake2b_update_scratch}
	add r12, r14
	mov rsi, r12
	mov rdi, rbx
	mov rdx, rbx
	add rdx, 768
	mov rcx, rbx
	add rcx, 192
	call {vg_blake2b_finalize_scratch}
	mov r14, rbp
	mov eax, 64
	mov rdx, rbx
	add rdx, 768
20:
	movzx ecx, BYTE PTR [rdx]
	mov BYTE PTR [r14], cl
	add rdx, 1
	add r14, 1
	sub rax, 1
	jne 20b
	mov r14, QWORD PTR [rbp+232]
	mov rax, QWORD PTR [rbp+240]
	mov ecx, 0
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
21:
	mov QWORD PTR [r14], rcx
	add r14, 8
	sub rax, 1
	jne 21b
	mov r14, QWORD PTR [rbp+232]
	mov r12d, 0
	mov r15, QWORD PTR [rbp+184]
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
	add r13, r13
22:
	mov eax, 0
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime}
	add r14, 1024
	mov eax, 1
	mov DWORD PTR [rbp+64], eax
	mov DWORD PTR [rbp+68], r12d
	mov rdi, rbp
	mov esi, 72
	mov rdx, r14
	mov ecx, 1024
	mov r8, rbx
	call {vg_argon2_hprime}
	add r14, r13
	sub r14, 1024
	add r12, 1
	sub r15, 1
	jne 22b
	mov r12, r13
	shr r12, 10
	shr r13, 12
	mov rax, 0
	mov QWORD PTR [rbp], rax
	mov rbx, 0
	mov r14, 0
23:
	mov r14, 0
24:
	mov rbx, 0
25:
	mov rax, 0
	mov QWORD PTR [rbp+8], rax
	mov rcx, QWORD PTR [rbp]
	or rcx, r14
	cmp rcx, 0
	je 26f
	mov r15, 0
	jmp 27f
26:
	mov r15, 2
27:
	cmp r15, r13
	jb 28f
	jmp 29f
28:
210:
	mov rax, QWORD PTR [rbp+112]
	mov r10, rax
	xor r10, 1
	cmp r10, 1
	sbb r10, r10
	mov r8, rax
	xor r8, 2
	cmp r8, 1
	sbb r8, r8
	mov r9, QWORD PTR [rbp]
	cmp r9, 1
	sbb r9, r9
	cmp r14, 2
	sbb r11, r11
	and r8, r9
	and r8, r11
	or r10, r8
	and r10, 1
	cmp r10, 0
	je 211f
	mov rax, r15
	shr rax, 7
	add rax, 1
	cmp rax, QWORD PTR [rbp+8]
	je 213f
	mov QWORD PTR [rbp+8], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 7168
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
	mov rdi, QWORD PTR [rbp+248]
	add rdi, 5120
	mov rax, QWORD PTR [rbp]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], r14
	mov rax, QWORD PTR [rbp+240]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rbp+72]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rbp+112]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rbp+8]
	mov QWORD PTR [rdi+48], rax
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 5120
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress}
	mov rcx, QWORD PTR [rbp+248]
	mov rdi, rcx
	add rdi, 7168
	mov rsi, rcx
	add rsi, 4096
	mov rdx, rcx
	add rdx, 6144
	call {vg_argon2_compress}
	jmp 214f
213:
214:
	mov rcx, QWORD PTR [rbp+248]
	mov rax, r15
	and rax, 127
	mov rdi, QWORD PTR [rcx+rax*8+6144]
	jmp 212f
211:
	mov r8, QWORD PTR [rbp+232]
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 215f
	mov rdi, rcx
	jmp 216f
215:
	mov rdi, r12
216:
	sub rdi, 1
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rdi, QWORD PTR [rax]
212:
	mov rsi, QWORD PTR [rbp+184]
	mov r11, rdi
	shr rdi, 32
	mov r8d, 0
	mov r9d, 0
	mov eax, 0
	cmp rax, 0
	mov rcx, rdi
	shr rcx, 32
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 31
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 30
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 29
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 28
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 27
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 26
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 25
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 24
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 23
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 22
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 21
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 20
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 19
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 18
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 17
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 16
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 15
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 14
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 13
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 12
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 11
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 10
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 9
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 8
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 7
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 6
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 5
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 4
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 3
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 2
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov rcx, rdi
	shr rcx, 1
	adc r8, r8
	mov r10, r8
	sub r8, rsi
	sbb rax, rax
	xor r10, r8
	and r10, rax
	xor r8, r10
	add rax, 1
	add r9, r9
	add r9, rax
	mov r9, QWORD PTR [rbp]
	mov rax, r9
	or rax, r14
	je 217f
	jmp 218f
217:
	mov r8, rbx
218:
	mov rdi, r8
	mov rsi, rbx
	cmp r9, 0
	je 219f
	mov rax, r14
	add rax, 1
	mul r13
	mov r10, rax
	cmp r14, 3
	je 221f
	jmp 222f
221:
	mov r10, 0
222:
	jmp 220f
219:
	mov r10, 0
220:
	cmp r9, 0
	je 223f
	mov rax, r12
	sub rax, r13
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
	jmp 224f
223:
	mov rax, r13
	mul r14
	mov rcx, rax
	mov rdx, rax
	add rdx, r15
	sub rdx, 1
224:
	mov r8, r15
	sub r8, 1
	sbb r9, r9
	add rcx, r9
	mov rax, rdi
	xor rax, rsi
	sub rax, 1
	sbb rax, rax
	mov r8, rcx
	xor rdx, rcx
	and rdx, rax
	xor r8, rdx
	mov r9, rdi
	mov rdi, r11
	mov rsi, r8
	mov eax, edi
	mul rax
	shr rax, 32
	mul rsi
	shr rax, 32
	mov rcx, rsi
	sub rcx, 1
	sub rcx, rax
	mov rax, rcx
	mov rdi, rax
	add rdi, r10
	mov rsi, r12
	mov r10, rdi
	sub rdi, rsi
	sbb rax, rax
	xor r10, rdi
	and r10, rax
	xor rdi, r10
	mov r8, QWORD PTR [rbp+232]
	mov rsi, rdi
	mov rax, r14
	mul r13
	mov rcx, rax
	add rcx, r15
	cmp rcx, 0
	je 225f
	mov rdi, rcx
	jmp 226f
225:
	mov rdi, r12
226:
	sub rdi, 1
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r10, rax
	mov rcx, rdi
	mov rax, rbx
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov r11, rax
	mov rcx, rsi
	mov rax, r9
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r11
	mov QWORD PTR [rbp+16], r10
	mov rcx, QWORD PTR [rbp+248]
	mov rdx, rcx
	add rdx, 4096
	call {vg_argon2_compress}
	mov rdi, QWORD PTR [rbp+16]
	mov rsi, QWORD PTR [rbp+248]
	add rsi, 4096
	mov r9, QWORD PTR [rbp]
	cmp r9, 0
	je 227f
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	jmp 228f
227:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	mov QWORD PTR [rdi+1016], rax
228:
	add r15, 1
	cmp r15, r13
	jb 210b
29:
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 25b
	add r14, 1
	cmp r14, 4
	jb 24b
	mov rax, QWORD PTR [rbp]
	add rax, 1
	mov QWORD PTR [rbp], rax
	cmp rax, QWORD PTR [rbp+72]
	jb 23b
	mov rdi, QWORD PTR [rbp+232]
	mov rbx, 0
	mov rax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov QWORD PTR [rdi+96], rax
	mov QWORD PTR [rdi+104], rax
	mov QWORD PTR [rdi+112], rax
	mov QWORD PTR [rdi+120], rax
	mov QWORD PTR [rdi+128], rax
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rax
	mov QWORD PTR [rdi+152], rax
	mov QWORD PTR [rdi+160], rax
	mov QWORD PTR [rdi+168], rax
	mov QWORD PTR [rdi+176], rax
	mov QWORD PTR [rdi+184], rax
	mov QWORD PTR [rdi+192], rax
	mov QWORD PTR [rdi+200], rax
	mov QWORD PTR [rdi+208], rax
	mov QWORD PTR [rdi+216], rax
	mov QWORD PTR [rdi+224], rax
	mov QWORD PTR [rdi+232], rax
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+248], rax
	mov QWORD PTR [rdi+256], rax
	mov QWORD PTR [rdi+264], rax
	mov QWORD PTR [rdi+272], rax
	mov QWORD PTR [rdi+280], rax
	mov QWORD PTR [rdi+288], rax
	mov QWORD PTR [rdi+296], rax
	mov QWORD PTR [rdi+304], rax
	mov QWORD PTR [rdi+312], rax
	mov QWORD PTR [rdi+320], rax
	mov QWORD PTR [rdi+328], rax
	mov QWORD PTR [rdi+336], rax
	mov QWORD PTR [rdi+344], rax
	mov QWORD PTR [rdi+352], rax
	mov QWORD PTR [rdi+360], rax
	mov QWORD PTR [rdi+368], rax
	mov QWORD PTR [rdi+376], rax
	mov QWORD PTR [rdi+384], rax
	mov QWORD PTR [rdi+392], rax
	mov QWORD PTR [rdi+400], rax
	mov QWORD PTR [rdi+408], rax
	mov QWORD PTR [rdi+416], rax
	mov QWORD PTR [rdi+424], rax
	mov QWORD PTR [rdi+432], rax
	mov QWORD PTR [rdi+440], rax
	mov QWORD PTR [rdi+448], rax
	mov QWORD PTR [rdi+456], rax
	mov QWORD PTR [rdi+464], rax
	mov QWORD PTR [rdi+472], rax
	mov QWORD PTR [rdi+480], rax
	mov QWORD PTR [rdi+488], rax
	mov QWORD PTR [rdi+496], rax
	mov QWORD PTR [rdi+504], rax
	mov QWORD PTR [rdi+512], rax
	mov QWORD PTR [rdi+520], rax
	mov QWORD PTR [rdi+528], rax
	mov QWORD PTR [rdi+536], rax
	mov QWORD PTR [rdi+544], rax
	mov QWORD PTR [rdi+552], rax
	mov QWORD PTR [rdi+560], rax
	mov QWORD PTR [rdi+568], rax
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+632], rax
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+696], rax
	mov QWORD PTR [rdi+704], rax
	mov QWORD PTR [rdi+712], rax
	mov QWORD PTR [rdi+720], rax
	mov QWORD PTR [rdi+728], rax
	mov QWORD PTR [rdi+736], rax
	mov QWORD PTR [rdi+744], rax
	mov QWORD PTR [rdi+752], rax
	mov QWORD PTR [rdi+760], rax
	mov QWORD PTR [rdi+768], rax
	mov QWORD PTR [rdi+776], rax
	mov QWORD PTR [rdi+784], rax
	mov QWORD PTR [rdi+792], rax
	mov QWORD PTR [rdi+800], rax
	mov QWORD PTR [rdi+808], rax
	mov QWORD PTR [rdi+816], rax
	mov QWORD PTR [rdi+824], rax
	mov QWORD PTR [rdi+832], rax
	mov QWORD PTR [rdi+840], rax
	mov QWORD PTR [rdi+848], rax
	mov QWORD PTR [rdi+856], rax
	mov QWORD PTR [rdi+864], rax
	mov QWORD PTR [rdi+872], rax
	mov QWORD PTR [rdi+880], rax
	mov QWORD PTR [rdi+888], rax
	mov QWORD PTR [rdi+896], rax
	mov QWORD PTR [rdi+904], rax
	mov QWORD PTR [rdi+912], rax
	mov QWORD PTR [rdi+920], rax
	mov QWORD PTR [rdi+928], rax
	mov QWORD PTR [rdi+936], rax
	mov QWORD PTR [rdi+944], rax
	mov QWORD PTR [rdi+952], rax
	mov QWORD PTR [rdi+960], rax
	mov QWORD PTR [rdi+968], rax
	mov QWORD PTR [rdi+976], rax
	mov QWORD PTR [rdi+984], rax
	mov QWORD PTR [rdi+992], rax
	mov QWORD PTR [rdi+1000], rax
	mov QWORD PTR [rdi+1008], rax
	mov QWORD PTR [rdi+1016], rax
229:
	mov r8, QWORD PTR [rbp+232]
	mov rax, rbx
	mov rcx, r12
	sub rcx, 1
	mul r12
	add rax, rcx
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov rsi, rax
	mov rdi, r8
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [rsi+8]
	xor rax, QWORD PTR [rdi+8]
	mov QWORD PTR [rdi+8], rax
	mov rax, QWORD PTR [rsi+16]
	xor rax, QWORD PTR [rdi+16]
	mov QWORD PTR [rdi+16], rax
	mov rax, QWORD PTR [rsi+24]
	xor rax, QWORD PTR [rdi+24]
	mov QWORD PTR [rdi+24], rax
	mov rax, QWORD PTR [rsi+32]
	xor rax, QWORD PTR [rdi+32]
	mov QWORD PTR [rdi+32], rax
	mov rax, QWORD PTR [rsi+40]
	xor rax, QWORD PTR [rdi+40]
	mov QWORD PTR [rdi+40], rax
	mov rax, QWORD PTR [rsi+48]
	xor rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [rsi+56]
	xor rax, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [rsi+64]
	xor rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	mov rax, QWORD PTR [rsi+72]
	xor rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+72], rax
	mov rax, QWORD PTR [rsi+80]
	xor rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+80], rax
	mov rax, QWORD PTR [rsi+88]
	xor rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+88], rax
	mov rax, QWORD PTR [rsi+96]
	xor rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+96], rax
	mov rax, QWORD PTR [rsi+104]
	xor rax, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+104], rax
	mov rax, QWORD PTR [rsi+112]
	xor rax, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+112], rax
	mov rax, QWORD PTR [rsi+120]
	xor rax, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+120], rax
	mov rax, QWORD PTR [rsi+128]
	xor rax, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rsi+136]
	xor rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rsi+144]
	xor rax, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rsi+152]
	xor rax, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+152], rax
	mov rax, QWORD PTR [rsi+160]
	xor rax, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+160], rax
	mov rax, QWORD PTR [rsi+168]
	xor rax, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rax
	mov rax, QWORD PTR [rsi+176]
	xor rax, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+176], rax
	mov rax, QWORD PTR [rsi+184]
	xor rax, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+184], rax
	mov rax, QWORD PTR [rsi+192]
	xor rax, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rsi+200]
	xor rax, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+200], rax
	mov rax, QWORD PTR [rsi+208]
	xor rax, QWORD PTR [rdi+208]
	mov QWORD PTR [rdi+208], rax
	mov rax, QWORD PTR [rsi+216]
	xor rax, QWORD PTR [rdi+216]
	mov QWORD PTR [rdi+216], rax
	mov rax, QWORD PTR [rsi+224]
	xor rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rax
	mov rax, QWORD PTR [rsi+232]
	xor rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rsi+240]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	mov rax, QWORD PTR [rsi+248]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+248], rax
	mov rax, QWORD PTR [rsi+256]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [rdi+256], rax
	mov rax, QWORD PTR [rsi+264]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [rdi+264], rax
	mov rax, QWORD PTR [rsi+272]
	xor rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rdi+272], rax
	mov rax, QWORD PTR [rsi+280]
	xor rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+280], rax
	mov rax, QWORD PTR [rsi+288]
	xor rax, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+288], rax
	mov rax, QWORD PTR [rsi+296]
	xor rax, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+296], rax
	mov rax, QWORD PTR [rsi+304]
	xor rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+304], rax
	mov rax, QWORD PTR [rsi+312]
	xor rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+312], rax
	mov rax, QWORD PTR [rsi+320]
	xor rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+320], rax
	mov rax, QWORD PTR [rsi+328]
	xor rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+328], rax
	mov rax, QWORD PTR [rsi+336]
	xor rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+336], rax
	mov rax, QWORD PTR [rsi+344]
	xor rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+344], rax
	mov rax, QWORD PTR [rsi+352]
	xor rax, QWORD PTR [rdi+352]
	mov QWORD PTR [rdi+352], rax
	mov rax, QWORD PTR [rsi+360]
	xor rax, QWORD PTR [rdi+360]
	mov QWORD PTR [rdi+360], rax
	mov rax, QWORD PTR [rsi+368]
	xor rax, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+368], rax
	mov rax, QWORD PTR [rsi+376]
	xor rax, QWORD PTR [rdi+376]
	mov QWORD PTR [rdi+376], rax
	mov rax, QWORD PTR [rsi+384]
	xor rax, QWORD PTR [rdi+384]
	mov QWORD PTR [rdi+384], rax
	mov rax, QWORD PTR [rsi+392]
	xor rax, QWORD PTR [rdi+392]
	mov QWORD PTR [rdi+392], rax
	mov rax, QWORD PTR [rsi+400]
	xor rax, QWORD PTR [rdi+400]
	mov QWORD PTR [rdi+400], rax
	mov rax, QWORD PTR [rsi+408]
	xor rax, QWORD PTR [rdi+408]
	mov QWORD PTR [rdi+408], rax
	mov rax, QWORD PTR [rsi+416]
	xor rax, QWORD PTR [rdi+416]
	mov QWORD PTR [rdi+416], rax
	mov rax, QWORD PTR [rsi+424]
	xor rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+424], rax
	mov rax, QWORD PTR [rsi+432]
	xor rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+432], rax
	mov rax, QWORD PTR [rsi+440]
	xor rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+440], rax
	mov rax, QWORD PTR [rsi+448]
	xor rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+448], rax
	mov rax, QWORD PTR [rsi+456]
	xor rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+456], rax
	mov rax, QWORD PTR [rsi+464]
	xor rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+464], rax
	mov rax, QWORD PTR [rsi+472]
	xor rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+472], rax
	mov rax, QWORD PTR [rsi+480]
	xor rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+480], rax
	mov rax, QWORD PTR [rsi+488]
	xor rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+488], rax
	mov rax, QWORD PTR [rsi+496]
	xor rax, QWORD PTR [rdi+496]
	mov QWORD PTR [rdi+496], rax
	mov rax, QWORD PTR [rsi+504]
	xor rax, QWORD PTR [rdi+504]
	mov QWORD PTR [rdi+504], rax
	mov rax, QWORD PTR [rsi+512]
	xor rax, QWORD PTR [rdi+512]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rsi+520]
	xor rax, QWORD PTR [rdi+520]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rsi+528]
	xor rax, QWORD PTR [rdi+528]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rsi+536]
	xor rax, QWORD PTR [rdi+536]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rsi+544]
	xor rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rsi+552]
	xor rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rsi+560]
	xor rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rsi+568]
	xor rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rsi+576]
	xor rax, QWORD PTR [rdi+576]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rsi+584]
	xor rax, QWORD PTR [rdi+584]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rsi+592]
	xor rax, QWORD PTR [rdi+592]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rsi+600]
	xor rax, QWORD PTR [rdi+600]
	mov QWORD PTR [rdi+600], rax
	mov rax, QWORD PTR [rsi+608]
	xor rax, QWORD PTR [rdi+608]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rsi+616]
	xor rax, QWORD PTR [rdi+616]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rsi+624]
	xor rax, QWORD PTR [rdi+624]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rsi+632]
	xor rax, QWORD PTR [rdi+632]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rsi+640]
	xor rax, QWORD PTR [rdi+640]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rsi+648]
	xor rax, QWORD PTR [rdi+648]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rsi+656]
	xor rax, QWORD PTR [rdi+656]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rsi+664]
	xor rax, QWORD PTR [rdi+664]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rsi+672]
	xor rax, QWORD PTR [rdi+672]
	mov QWORD PTR [rdi+672], rax
	mov rax, QWORD PTR [rsi+680]
	xor rax, QWORD PTR [rdi+680]
	mov QWORD PTR [rdi+680], rax
	mov rax, QWORD PTR [rsi+688]
	xor rax, QWORD PTR [rdi+688]
	mov QWORD PTR [rdi+688], rax
	mov rax, QWORD PTR [rsi+696]
	xor rax, QWORD PTR [rdi+696]
	mov QWORD PTR [rdi+696], rax
	mov rax, QWORD PTR [rsi+704]
	xor rax, QWORD PTR [rdi+704]
	mov QWORD PTR [rdi+704], rax
	mov rax, QWORD PTR [rsi+712]
	xor rax, QWORD PTR [rdi+712]
	mov QWORD PTR [rdi+712], rax
	mov rax, QWORD PTR [rsi+720]
	xor rax, QWORD PTR [rdi+720]
	mov QWORD PTR [rdi+720], rax
	mov rax, QWORD PTR [rsi+728]
	xor rax, QWORD PTR [rdi+728]
	mov QWORD PTR [rdi+728], rax
	mov rax, QWORD PTR [rsi+736]
	xor rax, QWORD PTR [rdi+736]
	mov QWORD PTR [rdi+736], rax
	mov rax, QWORD PTR [rsi+744]
	xor rax, QWORD PTR [rdi+744]
	mov QWORD PTR [rdi+744], rax
	mov rax, QWORD PTR [rsi+752]
	xor rax, QWORD PTR [rdi+752]
	mov QWORD PTR [rdi+752], rax
	mov rax, QWORD PTR [rsi+760]
	xor rax, QWORD PTR [rdi+760]
	mov QWORD PTR [rdi+760], rax
	mov rax, QWORD PTR [rsi+768]
	xor rax, QWORD PTR [rdi+768]
	mov QWORD PTR [rdi+768], rax
	mov rax, QWORD PTR [rsi+776]
	xor rax, QWORD PTR [rdi+776]
	mov QWORD PTR [rdi+776], rax
	mov rax, QWORD PTR [rsi+784]
	xor rax, QWORD PTR [rdi+784]
	mov QWORD PTR [rdi+784], rax
	mov rax, QWORD PTR [rsi+792]
	xor rax, QWORD PTR [rdi+792]
	mov QWORD PTR [rdi+792], rax
	mov rax, QWORD PTR [rsi+800]
	xor rax, QWORD PTR [rdi+800]
	mov QWORD PTR [rdi+800], rax
	mov rax, QWORD PTR [rsi+808]
	xor rax, QWORD PTR [rdi+808]
	mov QWORD PTR [rdi+808], rax
	mov rax, QWORD PTR [rsi+816]
	xor rax, QWORD PTR [rdi+816]
	mov QWORD PTR [rdi+816], rax
	mov rax, QWORD PTR [rsi+824]
	xor rax, QWORD PTR [rdi+824]
	mov QWORD PTR [rdi+824], rax
	mov rax, QWORD PTR [rsi+832]
	xor rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+832], rax
	mov rax, QWORD PTR [rsi+840]
	xor rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+840], rax
	mov rax, QWORD PTR [rsi+848]
	xor rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+848], rax
	mov rax, QWORD PTR [rsi+856]
	xor rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+856], rax
	mov rax, QWORD PTR [rsi+864]
	xor rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+864], rax
	mov rax, QWORD PTR [rsi+872]
	xor rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+872], rax
	mov rax, QWORD PTR [rsi+880]
	xor rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+880], rax
	mov rax, QWORD PTR [rsi+888]
	xor rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+888], rax
	mov rax, QWORD PTR [rsi+896]
	xor rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+896], rax
	mov rax, QWORD PTR [rsi+904]
	xor rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+904], rax
	mov rax, QWORD PTR [rsi+912]
	xor rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+912], rax
	mov rax, QWORD PTR [rsi+920]
	xor rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+920], rax
	mov rax, QWORD PTR [rsi+928]
	xor rax, QWORD PTR [rdi+928]
	mov QWORD PTR [rdi+928], rax
	mov rax, QWORD PTR [rsi+936]
	xor rax, QWORD PTR [rdi+936]
	mov QWORD PTR [rdi+936], rax
	mov rax, QWORD PTR [rsi+944]
	xor rax, QWORD PTR [rdi+944]
	mov QWORD PTR [rdi+944], rax
	mov rax, QWORD PTR [rsi+952]
	xor rax, QWORD PTR [rdi+952]
	mov QWORD PTR [rdi+952], rax
	mov rax, QWORD PTR [rsi+960]
	xor rax, QWORD PTR [rdi+960]
	mov QWORD PTR [rdi+960], rax
	mov rax, QWORD PTR [rsi+968]
	xor rax, QWORD PTR [rdi+968]
	mov QWORD PTR [rdi+968], rax
	mov rax, QWORD PTR [rsi+976]
	xor rax, QWORD PTR [rdi+976]
	mov QWORD PTR [rdi+976], rax
	mov rax, QWORD PTR [rsi+984]
	xor rax, QWORD PTR [rdi+984]
	mov QWORD PTR [rdi+984], rax
	mov rax, QWORD PTR [rsi+992]
	xor rax, QWORD PTR [rdi+992]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rsi+1000]
	xor rax, QWORD PTR [rdi+1000]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rsi+1008]
	xor rax, QWORD PTR [rdi+1008]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rsi+1016]
	xor rax, QWORD PTR [rdi+1016]
	mov QWORD PTR [rdi+1016], rax
	add rbx, 1
	cmp rbx, QWORD PTR [rbp+184]
	jb 229b
	mov rdi, QWORD PTR [rbp+232]
	mov rsi, 1024
	mov rdx, QWORD PTR [rbp+256]
	mov rcx, QWORD PTR [rbp+264]
	mov r8, QWORD PTR [rbp+248]
	call {vg_argon2_hprime}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop r15
	pop r14
	pop r13
	pop r12
	pop rbp
	pop rbx
	ret
	.p2align 6
