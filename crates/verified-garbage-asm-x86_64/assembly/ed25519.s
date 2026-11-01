// The functions of `src/ed25519.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_public_key_expanded:
	push rdi
	push rsi
	push rdx
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+40]
	mov rcx, QWORD PTR [rsp+32]
	mov rdx, QWORD PTR [rax]
	mov QWORD PTR [rcx+1568], rdx
	mov rdx, QWORD PTR [rax+8]
	mov QWORD PTR [rcx+1576], rdx
	mov rdx, QWORD PTR [rax+16]
	mov QWORD PTR [rcx+1584], rdx
	mov rdx, QWORD PTR [rax+24]
	mov QWORD PTR [rcx+1592], rdx
	mov rdx, QWORD PTR [rax+32]
	mov QWORD PTR [rcx+1600], rdx
	mov rdx, QWORD PTR [rax+40]
	mov QWORD PTR [rcx+1608], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rcx+1616], rdx
	mov rdx, QWORD PTR [rax+56]
	mov QWORD PTR [rcx+1624], rdx
	mov rdi, QWORD PTR [rsp+48]
	mov rsi, rsp
	mov rdx, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rdx+1568]
	mov r9, QWORD PTR [rdx+1576]
	mov r10, QWORD PTR [rdx+1584]
	mov r11, QWORD PTR [rdx+1592]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	call {vg_ed25519_scalar_base}
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	ret
	.p2align 6

vg_ed25519_public_key_expanded_adx:
	push rdi
	push rsi
	push rdx
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+40]
	mov rcx, QWORD PTR [rsp+32]
	mov rdx, QWORD PTR [rax]
	mov QWORD PTR [rcx+1568], rdx
	mov rdx, QWORD PTR [rax+8]
	mov QWORD PTR [rcx+1576], rdx
	mov rdx, QWORD PTR [rax+16]
	mov QWORD PTR [rcx+1584], rdx
	mov rdx, QWORD PTR [rax+24]
	mov QWORD PTR [rcx+1592], rdx
	mov rdx, QWORD PTR [rax+32]
	mov QWORD PTR [rcx+1600], rdx
	mov rdx, QWORD PTR [rax+40]
	mov QWORD PTR [rcx+1608], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rcx+1616], rdx
	mov rdx, QWORD PTR [rax+56]
	mov QWORD PTR [rcx+1624], rdx
	mov rdi, QWORD PTR [rsp+48]
	mov rsi, rsp
	mov rdx, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rdx+1568]
	mov r9, QWORD PTR [rdx+1576]
	mov r10, QWORD PTR [rdx+1584]
	mov r11, QWORD PTR [rdx+1592]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	call {vg_ed25519_scalar_base_adx}
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	ret
	.p2align 6

vg_ed25519_public_key_expanded_ifma:
	push rdi
	push rsi
	push rdx
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+40]
	mov rcx, QWORD PTR [rsp+32]
	mov rdx, QWORD PTR [rax]
	mov QWORD PTR [rcx+1568], rdx
	mov rdx, QWORD PTR [rax+8]
	mov QWORD PTR [rcx+1576], rdx
	mov rdx, QWORD PTR [rax+16]
	mov QWORD PTR [rcx+1584], rdx
	mov rdx, QWORD PTR [rax+24]
	mov QWORD PTR [rcx+1592], rdx
	mov rdx, QWORD PTR [rax+32]
	mov QWORD PTR [rcx+1600], rdx
	mov rdx, QWORD PTR [rax+40]
	mov QWORD PTR [rcx+1608], rdx
	mov rdx, QWORD PTR [rax+48]
	mov QWORD PTR [rcx+1616], rdx
	mov rdx, QWORD PTR [rax+56]
	mov QWORD PTR [rcx+1624], rdx
	mov rdi, QWORD PTR [rsp+48]
	mov rsi, rsp
	mov rdx, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rdx+1568]
	mov r9, QWORD PTR [rdx+1576]
	mov r10, QWORD PTR [rdx+1584]
	mov r11, QWORD PTR [rdx+1592]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	call {vg_ed25519_scalar_base_ifma}
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	ret
	.p2align 6

vg_ed25519_verify:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation}
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

vg_ed25519_sign_expanded:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
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
	ret
	.p2align 6

vg_ed25519_verify_adx:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation_adx}
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

vg_ed25519_sign_expanded_adx:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base_adx}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
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
	ret
	.p2align 6

vg_ed25519_verify_ifma:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation_ifma}
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

vg_ed25519_sign_expanded_ifma:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base_ifma}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
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
	ret
	.p2align 6

vg_ed25519_verify_avx2:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation}
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

vg_ed25519_sign_expanded_avx2:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
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
	ret
	.p2align 6

vg_ed25519_verify_avx2_adx:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation_adx}
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

vg_ed25519_sign_expanded_avx2_adx:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base_adx}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
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
	ret
	.p2align 6

vg_ed25519_verify_avx2_ifma:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation_ifma}
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

vg_ed25519_sign_expanded_avx2_ifma:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base_ifma}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
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
	ret
	.p2align 6

vg_ed25519_verify_shani:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation}
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

vg_ed25519_sign_expanded_shani:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
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
	ret
	.p2align 6

vg_ed25519_verify_shani_adx:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation_adx}
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

vg_ed25519_sign_expanded_shani_adx:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base_adx}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
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
	ret
	.p2align 6

vg_ed25519_verify_shani_ifma:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation_ifma}
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

vg_ed25519_sign_expanded_shani_ifma:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base_ifma}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
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
	ret
	.p2align 6
