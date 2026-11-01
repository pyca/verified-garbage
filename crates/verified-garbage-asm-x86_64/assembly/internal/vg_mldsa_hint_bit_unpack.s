// The functions of `src/internal/vg_mldsa_hint_bit_unpack.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_hint_bit_unpack:
	mov edx, edx
	mov eax, 0
	mov r9, rcx
	mov r10, r8
20:
	mov DWORD PTR [r9], eax
	add r9, 4
	sub r10, 1
	jne 20b
	mov r9, rdi
	add r9, rdx
	mov r10, rsi
	sub r10, rdx
21:
	cmp rdx, rax
	jae 22f
	jmp 23f
22:
	movzx r11d, BYTE PTR [r9]
	cmp r11, rax
	jb 24f
	cmp rdx, r11
	jb 26f
	cmp rax, r11
	jb 28f
	jmp 29f
28:
	movzx esi, BYTE PTR [rdi+rax*1]
	mov r8d, 1
	mov DWORD PTR [rcx+rsi*4], r8d
	add rax, 1
	cmp rax, r11
	jb 210f
	jmp 211f
210:
212:
	movzx r8d, BYTE PTR [rdi+rax*1-1]
	movzx esi, BYTE PTR [rdi+rax*1]
	cmp r8, rsi
	jb 213f
	mov eax, 256
	jmp 214f
213:
	mov r8d, 1
	mov DWORD PTR [rcx+rsi*4], r8d
	add rax, 1
214:
	cmp rax, r11
	jb 212b
211:
29:
	jmp 27f
26:
	mov eax, 256
27:
	jmp 25f
24:
	mov eax, 256
25:
23:
	add r9, 1
	add rcx, 1024
	sub r10, 1
	jne 21b
	cmp rax, rdx
	jb 215f
	jmp 216f
215:
217:
	movzx r8d, BYTE PTR [rdi+rax*1]
	cmp r8d, 0
	jne 218f
	add rax, 1
	jmp 219f
218:
	mov eax, 256
219:
	cmp rax, rdx
	jb 217b
216:
	cmp rdx, rax
	mov eax, 1
	sbb eax, 0
	ret
	.p2align 6
