// The functions of `src/internal/vg_p256_sub_mod_p.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p256_sub_mod_p:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3952], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov DWORD PTR [ebp+3940], ebx
	mov eax, DWORD PTR [ecx]
	sub eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [ecx+4]
	sbb eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [ecx+8]
	sbb eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [ecx+12]
	sbb eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [ecx+16]
	sbb eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3856], eax
	mov eax, DWORD PTR [ecx+20]
	sbb eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3860], eax
	mov eax, DWORD PTR [ecx+24]
	sbb eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3864], eax
	mov eax, DWORD PTR [ecx+28]
	sbb eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3868], eax
	sbb eax, eax
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov ebx, eax
	and ebx, 1
	mov edx, DWORD PTR [ebp+3840]
	add edx, eax
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3844]
	adc edx, eax
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3848]
	adc edx, eax
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3852]
	adc edx, 0
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3856]
	adc edx, 0
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3860]
	adc edx, 0
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3864]
	adc edx, ebx
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3868]
	adc edx, eax
	mov DWORD PTR [ecx+28], edx
	mov ebx, DWORD PTR [ebp+3940]
	mov ebp, DWORD PTR [ebp+3952]
	ret
	.p2align 6
