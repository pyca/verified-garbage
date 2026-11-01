// The functions of `src/ed448.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_public_key_adx:
	push rdi
	push rsi
	push rdx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+64]
	mov eax, 0
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
	mov rdi, QWORD PTR [rsp+64]
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+72]
	mov r8d, 57
	mov r9, QWORD PTR [rsp+64]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov esi, 136
	mov edx, 57
	mov ecx, 31
	mov r8, QWORD PTR [rsp+64]
	add r8, 256
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 1024
	mov r8d, 114
	mov r9, QWORD PTR [rsp+64]
	add r9, 256
	call {vg_keccak_squeeze_scratch}
	mov rdx, QWORD PTR [rsp+64]
	mov r8, QWORD PTR [rdx+1024]
	mov r9, QWORD PTR [rdx+1032]
	mov r10, QWORD PTR [rdx+1040]
	mov r11, QWORD PTR [rdx+1048]
	mov rax, QWORD PTR [rdx+1056]
	mov rcx, QWORD PTR [rdx+1064]
	mov rsi, QWORD PTR [rdx+1072]
	and r8, -4
	movabs rdi, -9223372036854775808
	or rsi, rdi
	mov edi, 0
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rsi
	mov QWORD PTR [rsp+56], rdi
	mov rdi, QWORD PTR [rsp+80]
	mov rsi, rsp
	mov rdx, QWORD PTR [rsp+64]
	call {vg_ed448_scalar_base_adx}
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov eax, 0
	mov ecx, 0
	mov esi, 0
	mov edi, 0
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rsi
	mov QWORD PTR [rsp+56], rdi
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
	ret
	.p2align 6

vg_ed448_sign_cached_adx:
	mov r10, QWORD PTR [rsp+8]
	mov r11, QWORD PTR [rsp+16]
	mov eax, 0
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
	push r11
	push rdi
	push r10
	push r9
	push r8
	push rcx
	push rdx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rsi
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
	movabs rax, 4049919570178697555
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+216]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rsp+8], rax
	mov rdi, QWORD PTR [rsp+248]
	mov eax, 0
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
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+136]
	mov r8d, 57
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 57
	mov ecx, 31
	mov r8, QWORD PTR [rsp+248]
	add r8, 256
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, rsp
	add rcx, 16
	mov r8d, 114
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_squeeze_scratch}
	mov r8, QWORD PTR [rsp+16]
	mov r9, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r11, QWORD PTR [rsp+40]
	mov rax, QWORD PTR [rsp+48]
	mov rcx, QWORD PTR [rsp+56]
	mov rsi, QWORD PTR [rsp+64]
	and r8, -4
	movabs rdi, -9223372036854775808
	or rsi, rdi
	mov edi, 0
	mov QWORD PTR [rsp+320], r8
	mov QWORD PTR [rsp+328], r9
	mov QWORD PTR [rsp+336], r10
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], rax
	mov QWORD PTR [rsp+360], rcx
	mov QWORD PTR [rsp+368], rsi
	mov QWORD PTR [rsp+376], rdi
	mov rdi, QWORD PTR [rsp+248]
	mov eax, 0
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
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, rsp
	add rcx, 0
	mov r8d, 10
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+216]
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, rsp
	add rcx, 73
	mov r8d, 57
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+232]
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+248]
	add r8, 256
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, rsp
	add rcx, 16
	mov r8d, 114
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_squeeze_scratch}
	mov rdi, rsp
	add rdi, 384
	mov rsi, rsp
	add rsi, 16
	mov rdx, QWORD PTR [rsp+248]
	call {vg_ed448_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 384
	mov rdx, QWORD PTR [rsp+248]
	call {vg_ed448_scalar_base_adx}
	mov rdi, QWORD PTR [rsp+248]
	mov eax, 0
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
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, rsp
	add rcx, 0
	mov r8d, 10
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+216]
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+240]
	mov r8d, 57
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+200]
	mov r8d, 57
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+232]
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+248]
	add r8, 256
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, rsp
	add rcx, 16
	mov r8d, 114
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_squeeze_scratch}
	mov rdi, rsp
	add rdi, 256
	mov rsi, rsp
	add rsi, 16
	mov rdx, QWORD PTR [rsp+248]
	call {vg_ed448_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 57
	mov rsi, rsp
	add rsi, 384
	mov rdx, rsp
	add rdx, 256
	mov rcx, rsp
	add rcx, 320
	mov r8, QWORD PTR [rsp+248]
	call {vg_ed448_scalar_mul_add}
	mov eax, 0
	mov QWORD PTR [rsp+320], rax
	mov QWORD PTR [rsp+328], rax
	mov QWORD PTR [rsp+336], rax
	mov QWORD PTR [rsp+344], rax
	mov QWORD PTR [rsp+352], rax
	mov QWORD PTR [rsp+360], rax
	mov QWORD PTR [rsp+368], rax
	mov QWORD PTR [rsp+376], rax
	mov QWORD PTR [rsp+384], rax
	mov QWORD PTR [rsp+392], rax
	mov QWORD PTR [rsp+400], rax
	mov QWORD PTR [rsp+408], rax
	mov QWORD PTR [rsp+416], rax
	mov QWORD PTR [rsp+424], rax
	mov QWORD PTR [rsp+432], rax
	mov QWORD PTR [rsp+440], rax
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	ret
	.p2align 6

vg_ed448_verify_adx:
	cmp rdx, 256
	jb 20f
	mov eax, 0
	jmp 21f
20:
	mov r11, QWORD PTR [rsp+8]
	mov eax, 0
	push r11
	push r9
	push r8
	push rcx
	push rdx
	push rsi
	push rdi
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
	movabs rax, 4049919570178697555
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+216]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rsp+8], rax
	mov rdi, QWORD PTR [rsp+248]
	mov eax, 0
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
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, rsp
	add rcx, 0
	mov r8d, 10
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+216]
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+240]
	mov r8d, 57
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+200]
	mov r8d, 57
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+232]
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+248]
	add r8, 256
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, rsp
	add rcx, 16
	mov r8d, 114
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_squeeze_scratch}
	mov rdi, rsp
	add rdi, 136
	mov rsi, rsp
	add rsi, 16
	mov rdx, QWORD PTR [rsp+248]
	call {vg_ed448_scalar_reduce}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+240]
	mov rdx, rsp
	add rdx, 136
	mov rcx, QWORD PTR [rsp+248]
	call {vg_ed448_verify_equation_adx}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
21:
	ret
	.p2align 6

vg_ed448_public_key:
	push rdi
	push rsi
	push rdx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+64]
	mov eax, 0
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
	mov rdi, QWORD PTR [rsp+64]
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+72]
	mov r8d, 57
	mov r9, QWORD PTR [rsp+64]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov esi, 136
	mov edx, 57
	mov ecx, 31
	mov r8, QWORD PTR [rsp+64]
	add r8, 256
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+64]
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+64]
	add rcx, 1024
	mov r8d, 114
	mov r9, QWORD PTR [rsp+64]
	add r9, 256
	call {vg_keccak_squeeze_scratch}
	mov rdx, QWORD PTR [rsp+64]
	mov r8, QWORD PTR [rdx+1024]
	mov r9, QWORD PTR [rdx+1032]
	mov r10, QWORD PTR [rdx+1040]
	mov r11, QWORD PTR [rdx+1048]
	mov rax, QWORD PTR [rdx+1056]
	mov rcx, QWORD PTR [rdx+1064]
	mov rsi, QWORD PTR [rdx+1072]
	and r8, -4
	movabs rdi, -9223372036854775808
	or rsi, rdi
	mov edi, 0
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rsi
	mov QWORD PTR [rsp+56], rdi
	mov rdi, QWORD PTR [rsp+80]
	mov rsi, rsp
	mov rdx, QWORD PTR [rsp+64]
	call {vg_ed448_scalar_base}
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov eax, 0
	mov ecx, 0
	mov esi, 0
	mov edi, 0
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rcx
	mov QWORD PTR [rsp+48], rsi
	mov QWORD PTR [rsp+56], rdi
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
	ret
	.p2align 6

vg_ed448_sign_cached:
	mov r10, QWORD PTR [rsp+8]
	mov r11, QWORD PTR [rsp+16]
	mov eax, 0
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
	push r11
	push rdi
	push r10
	push r9
	push r8
	push rcx
	push rdx
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rsi
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
	movabs rax, 4049919570178697555
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+216]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rsp+8], rax
	mov rdi, QWORD PTR [rsp+248]
	mov eax, 0
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
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, QWORD PTR [rsp+136]
	mov r8d, 57
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 57
	mov ecx, 31
	mov r8, QWORD PTR [rsp+248]
	add r8, 256
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, rsp
	add rcx, 16
	mov r8d, 114
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_squeeze_scratch}
	mov r8, QWORD PTR [rsp+16]
	mov r9, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r11, QWORD PTR [rsp+40]
	mov rax, QWORD PTR [rsp+48]
	mov rcx, QWORD PTR [rsp+56]
	mov rsi, QWORD PTR [rsp+64]
	and r8, -4
	movabs rdi, -9223372036854775808
	or rsi, rdi
	mov edi, 0
	mov QWORD PTR [rsp+320], r8
	mov QWORD PTR [rsp+328], r9
	mov QWORD PTR [rsp+336], r10
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], rax
	mov QWORD PTR [rsp+360], rcx
	mov QWORD PTR [rsp+368], rsi
	mov QWORD PTR [rsp+376], rdi
	mov rdi, QWORD PTR [rsp+248]
	mov eax, 0
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
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, rsp
	add rcx, 0
	mov r8d, 10
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+216]
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, rsp
	add rcx, 73
	mov r8d, 57
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+232]
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+248]
	add r8, 256
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, rsp
	add rcx, 16
	mov r8d, 114
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_squeeze_scratch}
	mov rdi, rsp
	add rdi, 384
	mov rsi, rsp
	add rsi, 16
	mov rdx, QWORD PTR [rsp+248]
	call {vg_ed448_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 384
	mov rdx, QWORD PTR [rsp+248]
	call {vg_ed448_scalar_base}
	mov rdi, QWORD PTR [rsp+248]
	mov eax, 0
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
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, rsp
	add rcx, 0
	mov r8d, 10
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+216]
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+240]
	mov r8d, 57
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+200]
	mov r8d, 57
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+232]
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+248]
	add r8, 256
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, rsp
	add rcx, 16
	mov r8d, 114
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_squeeze_scratch}
	mov rdi, rsp
	add rdi, 256
	mov rsi, rsp
	add rsi, 16
	mov rdx, QWORD PTR [rsp+248]
	call {vg_ed448_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 57
	mov rsi, rsp
	add rsi, 384
	mov rdx, rsp
	add rdx, 256
	mov rcx, rsp
	add rcx, 320
	mov r8, QWORD PTR [rsp+248]
	call {vg_ed448_scalar_mul_add}
	mov eax, 0
	mov QWORD PTR [rsp+320], rax
	mov QWORD PTR [rsp+328], rax
	mov QWORD PTR [rsp+336], rax
	mov QWORD PTR [rsp+344], rax
	mov QWORD PTR [rsp+352], rax
	mov QWORD PTR [rsp+360], rax
	mov QWORD PTR [rsp+368], rax
	mov QWORD PTR [rsp+376], rax
	mov QWORD PTR [rsp+384], rax
	mov QWORD PTR [rsp+392], rax
	mov QWORD PTR [rsp+400], rax
	mov QWORD PTR [rsp+408], rax
	mov QWORD PTR [rsp+416], rax
	mov QWORD PTR [rsp+424], rax
	mov QWORD PTR [rsp+432], rax
	mov QWORD PTR [rsp+440], rax
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	ret
	.p2align 6

vg_ed448_verify:
	cmp rdx, 256
	jb 20f
	mov eax, 0
	jmp 21f
20:
	mov r11, QWORD PTR [rsp+8]
	mov eax, 0
	push r11
	push r9
	push r8
	push rcx
	push rdx
	push rsi
	push rdi
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
	movabs rax, 4049919570178697555
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+216]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rsp+8], rax
	mov rdi, QWORD PTR [rsp+248]
	mov eax, 0
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
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, rsp
	add rcx, 0
	mov r8d, 10
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+216]
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+240]
	mov r8d, 57
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+200]
	mov r8d, 57
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov rcx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+232]
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_absorb_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov rdx, rax
	mov ecx, 31
	mov r8, QWORD PTR [rsp+248]
	add r8, 256
	call {vg_keccak_pad_scratch}
	mov rdi, QWORD PTR [rsp+248]
	mov esi, 136
	mov edx, 0
	mov rcx, rsp
	add rcx, 16
	mov r8d, 114
	mov r9, QWORD PTR [rsp+248]
	add r9, 256
	call {vg_keccak_squeeze_scratch}
	mov rdi, rsp
	add rdi, 136
	mov rsi, rsp
	add rsi, 16
	mov rdx, QWORD PTR [rsp+248]
	call {vg_ed448_scalar_reduce}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+240]
	mov rdx, rsp
	add rdx, 136
	mov rcx, QWORD PTR [rsp+248]
	call {vg_ed448_verify_equation}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
21:
	ret
	.p2align 6
