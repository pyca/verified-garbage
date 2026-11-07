// The functions of `src/internal/vg_ed25519_public_key_expanded.rs` of `verified-garbage-asm-x86_64`, as text: generated from
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
