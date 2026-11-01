// The functions of `src/internal/vg_mldsa_hint_bit_pack.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_hint_bit_pack:
	mov edx, edx
	mov eax, 0
	mov r9, rcx
	mov r10, r8
20:
	mov BYTE PTR [r9], al
	add r9, 1
	sub r10, 1
	jne 20b
	mov r9, rcx
	add r9, rdx
	mov r10, r8
	sub r10, rdx
21:
	mov r11d, 0
22:
	mov esi, DWORD PTR [rdi]
	cmp esi, 0
	jne 23f
	jmp 24f
23:
	mov BYTE PTR [rcx+rax*1], r11b
	add rax, 1
24:
	add rdi, 4
	add r11, 1
	cmp r11d, 256
	jne 22b
	mov BYTE PTR [r9], al
	add r9, 1
	sub r10, 1
	jne 21b
	ret
	.p2align 6
