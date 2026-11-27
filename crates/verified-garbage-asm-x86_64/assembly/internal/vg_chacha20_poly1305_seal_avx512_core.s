// The functions of `src/internal/vg_chacha20_poly1305_seal_avx512_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal_avx512_core:
	mov eax, 0
	mov rax, r9
	mov r10, r9
	sub r10, 961
	cmp r10, 64
	mov r10, 0
	cmovb rax, r10
	cmp rax, 640
	jb 20f
	lea rsp, [rsp-8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rsp], rax
	call {vg_chacha20_poly1305_seal_body_avx512}
	lea rsp, [rsp+8]
21:
	ret
20:
	lea rsp, [rsp-8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rsp], rax
	call {vg_chacha20_poly1305_seal_body_avx2}
	lea rsp, [rsp+8]
	jmp 21b
	.p2align 6
