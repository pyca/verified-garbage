// The functions of `src/internal/vg_mldsa_expand_mask_poly.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_expand_mask_poly:
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
	mov r8d, 640
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	cmp r12d, 131072
	je 20f
	mov rsi, rbx
	add rsi, 840
	mov rdi, rbp
	mov ecx, 64
22:
	mov eax, DWORD PTR [rsi]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+5]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+7]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 10
	add rdi, 16
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov rsi, rbx
	add rsi, 840
	mov rdi, rbp
	mov ecx, 64
23:
	mov eax, DWORD PTR [rsi]
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 2
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+4]
	shr eax, 4
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+6]
	shr eax, 6
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 9
	add rdi, 16
	sub rcx, 1
	jne 23b
21:
	mov rbp, QWORD PTR [rbx+2032]
	mov r12, QWORD PTR [rbx+2040]
	mov rbx, QWORD PTR [rbx+2024]
	ret
	.p2align 6
