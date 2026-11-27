// The functions of `src/internal/vg_p256_add_mod_p.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p256_add_mod_p:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3952], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov DWORD PTR [ebp+3940], ebx
	mov eax, DWORD PTR [ecx]
	add eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [ecx+4]
	adc eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [ecx+8]
	adc eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [ecx+12]
	adc eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [ecx+16]
	adc eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3856], eax
	mov eax, DWORD PTR [ecx+20]
	adc eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3860], eax
	mov eax, DWORD PTR [ecx+24]
	adc eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3864], eax
	mov eax, DWORD PTR [ecx+28]
	adc eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3868], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3872], eax
	mov eax, DWORD PTR [ebp+3840]
	sub eax, -1
	mov eax, DWORD PTR [ebp+3844]
	sbb eax, -1
	mov eax, DWORD PTR [ebp+3848]
	sbb eax, -1
	mov eax, DWORD PTR [ebp+3852]
	sbb eax, 0
	mov eax, DWORD PTR [ebp+3856]
	sbb eax, 0
	mov eax, DWORD PTR [ebp+3860]
	sbb eax, 0
	mov eax, DWORD PTR [ebp+3864]
	sbb eax, 1
	mov eax, DWORD PTR [ebp+3868]
	sbb eax, -1
	mov eax, DWORD PTR [ebp+3872]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov ebx, eax
	and ebx, 1
	mov edx, DWORD PTR [ebp+3840]
	sub edx, eax
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3844]
	sbb edx, eax
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3848]
	sbb edx, eax
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3852]
	sbb edx, 0
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3856]
	sbb edx, 0
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3860]
	sbb edx, 0
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3864]
	sbb edx, ebx
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3868]
	sbb edx, eax
	mov DWORD PTR [ecx+28], edx
	mov ebx, DWORD PTR [ebp+3940]
	mov ebp, DWORD PTR [ebp+3952]
	ret
	.p2align 6
