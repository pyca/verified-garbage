// The functions of `src/zeroize.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_zeroize:
	mov eax, 0
	mov ecx, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+8]
	shr edx, 5
	cmp edx, 0
	je 20f
22:
	mov DWORD PTR [ecx], eax
	mov DWORD PTR [ecx+4], eax
	mov DWORD PTR [ecx+8], eax
	mov DWORD PTR [ecx+12], eax
	mov DWORD PTR [ecx+16], eax
	mov DWORD PTR [ecx+20], eax
	mov DWORD PTR [ecx+24], eax
	mov DWORD PTR [ecx+28], eax
	add ecx, 32
	sub edx, 1
	jne 22b
	jmp 21f
20:
21:
	mov edx, DWORD PTR [esp+8]
	shr edx, 2
	and edx, 7
	cmp edx, 0
	je 23f
25:
	mov DWORD PTR [ecx], eax
	add ecx, 4
	sub edx, 1
	jne 25b
	jmp 24f
23:
24:
	mov edx, DWORD PTR [esp+8]
	and edx, 3
	cmp edx, 0
	je 26f
28:
	mov BYTE PTR [ecx], al
	add ecx, 1
	sub edx, 1
	jne 28b
	jmp 27f
26:
27:
	ret
	.p2align 6
