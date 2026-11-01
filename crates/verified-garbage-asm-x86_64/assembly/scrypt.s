// The functions of `src/scrypt.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
