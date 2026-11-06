// The functions of `src/x448.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x448_exchange:
	lea esp, [esp-16]
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp+12], eax
	call {vg_x448}
	lea esp, [esp+16]
	mov edx, DWORD PTR [esp+4]
	mov ecx, 0
	movzx eax, BYTE PTR [edx]
	or ecx, eax
	movzx eax, BYTE PTR [edx+1]
	or ecx, eax
	movzx eax, BYTE PTR [edx+2]
	or ecx, eax
	movzx eax, BYTE PTR [edx+3]
	or ecx, eax
	movzx eax, BYTE PTR [edx+4]
	or ecx, eax
	movzx eax, BYTE PTR [edx+5]
	or ecx, eax
	movzx eax, BYTE PTR [edx+6]
	or ecx, eax
	movzx eax, BYTE PTR [edx+7]
	or ecx, eax
	movzx eax, BYTE PTR [edx+8]
	or ecx, eax
	movzx eax, BYTE PTR [edx+9]
	or ecx, eax
	movzx eax, BYTE PTR [edx+10]
	or ecx, eax
	movzx eax, BYTE PTR [edx+11]
	or ecx, eax
	movzx eax, BYTE PTR [edx+12]
	or ecx, eax
	movzx eax, BYTE PTR [edx+13]
	or ecx, eax
	movzx eax, BYTE PTR [edx+14]
	or ecx, eax
	movzx eax, BYTE PTR [edx+15]
	or ecx, eax
	movzx eax, BYTE PTR [edx+16]
	or ecx, eax
	movzx eax, BYTE PTR [edx+17]
	or ecx, eax
	movzx eax, BYTE PTR [edx+18]
	or ecx, eax
	movzx eax, BYTE PTR [edx+19]
	or ecx, eax
	movzx eax, BYTE PTR [edx+20]
	or ecx, eax
	movzx eax, BYTE PTR [edx+21]
	or ecx, eax
	movzx eax, BYTE PTR [edx+22]
	or ecx, eax
	movzx eax, BYTE PTR [edx+23]
	or ecx, eax
	movzx eax, BYTE PTR [edx+24]
	or ecx, eax
	movzx eax, BYTE PTR [edx+25]
	or ecx, eax
	movzx eax, BYTE PTR [edx+26]
	or ecx, eax
	movzx eax, BYTE PTR [edx+27]
	or ecx, eax
	movzx eax, BYTE PTR [edx+28]
	or ecx, eax
	movzx eax, BYTE PTR [edx+29]
	or ecx, eax
	movzx eax, BYTE PTR [edx+30]
	or ecx, eax
	movzx eax, BYTE PTR [edx+31]
	or ecx, eax
	movzx eax, BYTE PTR [edx+32]
	or ecx, eax
	movzx eax, BYTE PTR [edx+33]
	or ecx, eax
	movzx eax, BYTE PTR [edx+34]
	or ecx, eax
	movzx eax, BYTE PTR [edx+35]
	or ecx, eax
	movzx eax, BYTE PTR [edx+36]
	or ecx, eax
	movzx eax, BYTE PTR [edx+37]
	or ecx, eax
	movzx eax, BYTE PTR [edx+38]
	or ecx, eax
	movzx eax, BYTE PTR [edx+39]
	or ecx, eax
	movzx eax, BYTE PTR [edx+40]
	or ecx, eax
	movzx eax, BYTE PTR [edx+41]
	or ecx, eax
	movzx eax, BYTE PTR [edx+42]
	or ecx, eax
	movzx eax, BYTE PTR [edx+43]
	or ecx, eax
	movzx eax, BYTE PTR [edx+44]
	or ecx, eax
	movzx eax, BYTE PTR [edx+45]
	or ecx, eax
	movzx eax, BYTE PTR [edx+46]
	or ecx, eax
	movzx eax, BYTE PTR [edx+47]
	or ecx, eax
	movzx eax, BYTE PTR [edx+48]
	or ecx, eax
	movzx eax, BYTE PTR [edx+49]
	or ecx, eax
	movzx eax, BYTE PTR [edx+50]
	or ecx, eax
	movzx eax, BYTE PTR [edx+51]
	or ecx, eax
	movzx eax, BYTE PTR [edx+52]
	or ecx, eax
	movzx eax, BYTE PTR [edx+53]
	or ecx, eax
	movzx eax, BYTE PTR [edx+54]
	or ecx, eax
	movzx eax, BYTE PTR [edx+55]
	or ecx, eax
	sub ecx, 1
	shr ecx, 31
	xor ecx, 1
	mov eax, ecx
	ret
	.p2align 6

vg_x448_base:
	mov eax, 0
	mov edx, 5
	push ebx
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push edx
	mov ebx, esp
	mov eax, DWORD PTR [esp+64]
	mov ecx, DWORD PTR [esp+68]
	mov edx, DWORD PTR [esp+72]
	push edx
	push ebx
	push ecx
	push eax
	call {vg_x448}
	pop eax
	pop eax
	pop eax
	pop eax
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
