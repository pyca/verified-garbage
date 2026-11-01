// The functions of `src/internal/vg_mldsa_power2round.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_power2round:
	mov ecx, 256
20:
	mov eax, DWORD PTR [rdi+rcx*4-4]
	add rax, 4095
	mov r8, rax
	shr r8, 13
	mov DWORD PTR [rsi+rcx*4-4], r8d
	and rax, 8191
	sub rax, 4095
	sbb r9, r9
	and r9, 8380417
	add rax, r9
	mov DWORD PTR [rdx+rcx*4-4], eax
	sub rcx, 1
	jne 20b
	ret
	.p2align 6
