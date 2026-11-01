// The functions of `src/internal/vg_p192_sub_mod_p.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_sub_mod_p:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3992], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	sub eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3904], eax
	mov eax, DWORD PTR [ecx+4]
	sbb eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3908], eax
	mov eax, DWORD PTR [ecx+8]
	sbb eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3912], eax
	mov eax, DWORD PTR [ecx+12]
	sbb eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3916], eax
	mov eax, DWORD PTR [ecx+16]
	sbb eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3920], eax
	mov eax, DWORD PTR [ecx+20]
	sbb eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3924], eax
	sbb eax, eax
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3956], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3960], edx
	mov edx, -2
	and edx, eax
	mov DWORD PTR [ebp+3964], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3968], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3972], edx
	mov edx, -1
	and edx, eax
	mov DWORD PTR [ebp+3976], edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3904]
	add edx, DWORD PTR [ebp+3956]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3908]
	adc edx, DWORD PTR [ebp+3960]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3912]
	adc edx, DWORD PTR [ebp+3964]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3916]
	adc edx, DWORD PTR [ebp+3968]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3920]
	adc edx, DWORD PTR [ebp+3972]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3924]
	adc edx, DWORD PTR [ebp+3976]
	mov DWORD PTR [ecx+20], edx
	mov ebp, DWORD PTR [ebp+3992]
	ret
	.p2align 6
