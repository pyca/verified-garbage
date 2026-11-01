// The functions of `src/internal/vg_brainpoolp256r1_add_mod_n.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp256r1_add_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3952], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
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
	sub eax, -1756866905
	mov DWORD PTR [ebp+3908], eax
	mov eax, DWORD PTR [ebp+3844]
	sbb eax, -1877078398
	mov DWORD PTR [ebp+3912], eax
	mov eax, DWORD PTR [ebp+3848]
	sbb eax, -1251891465
	mov DWORD PTR [ebp+3916], eax
	mov eax, DWORD PTR [ebp+3852]
	sbb eax, -1942390109
	mov DWORD PTR [ebp+3920], eax
	mov eax, DWORD PTR [ebp+3856]
	sbb eax, -1652322959
	mov DWORD PTR [ebp+3924], eax
	mov eax, DWORD PTR [ebp+3860]
	sbb eax, 1046874768
	mov DWORD PTR [ebp+3928], eax
	mov eax, DWORD PTR [ebp+3864]
	sbb eax, -1578194500
	mov DWORD PTR [ebp+3932], eax
	mov eax, DWORD PTR [ebp+3868]
	sbb eax, -1443145765
	mov DWORD PTR [ebp+3936], eax
	mov eax, DWORD PTR [ebp+3872]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3840]
	xor edx, DWORD PTR [ebp+3908]
	and edx, eax
	xor edx, DWORD PTR [ebp+3840]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3844]
	xor edx, DWORD PTR [ebp+3912]
	and edx, eax
	xor edx, DWORD PTR [ebp+3844]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3848]
	xor edx, DWORD PTR [ebp+3916]
	and edx, eax
	xor edx, DWORD PTR [ebp+3848]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3852]
	xor edx, DWORD PTR [ebp+3920]
	and edx, eax
	xor edx, DWORD PTR [ebp+3852]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3856]
	xor edx, DWORD PTR [ebp+3924]
	and edx, eax
	xor edx, DWORD PTR [ebp+3856]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3860]
	xor edx, DWORD PTR [ebp+3928]
	and edx, eax
	xor edx, DWORD PTR [ebp+3860]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3864]
	xor edx, DWORD PTR [ebp+3932]
	and edx, eax
	xor edx, DWORD PTR [ebp+3864]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3868]
	xor edx, DWORD PTR [ebp+3936]
	and edx, eax
	xor edx, DWORD PTR [ebp+3868]
	mov DWORD PTR [ecx+28], edx
	mov ebp, DWORD PTR [ebp+3952]
	ret
	.p2align 6
