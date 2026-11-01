// The functions of `src/internal/vg_p192_add_mod_n.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_add_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3992], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	add eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3904], eax
	mov eax, DWORD PTR [ecx+4]
	adc eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3908], eax
	mov eax, DWORD PTR [ecx+8]
	adc eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3912], eax
	mov eax, DWORD PTR [ecx+12]
	adc eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3916], eax
	mov eax, DWORD PTR [ecx+16]
	adc eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3920], eax
	mov eax, DWORD PTR [ecx+20]
	adc eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3924], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3928], eax
	mov eax, DWORD PTR [ebp+3904]
	sub eax, -1261295567
	mov DWORD PTR [ebp+3956], eax
	mov eax, DWORD PTR [ebp+3908]
	sbb eax, 342608305
	mov DWORD PTR [ebp+3960], eax
	mov eax, DWORD PTR [ebp+3912]
	sbb eax, -1713440714
	mov DWORD PTR [ebp+3964], eax
	mov eax, DWORD PTR [ebp+3916]
	sbb eax, -1
	mov DWORD PTR [ebp+3968], eax
	mov eax, DWORD PTR [ebp+3920]
	sbb eax, -1
	mov DWORD PTR [ebp+3972], eax
	mov eax, DWORD PTR [ebp+3924]
	sbb eax, -1
	mov DWORD PTR [ebp+3976], eax
	mov eax, DWORD PTR [ebp+3928]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3904]
	xor edx, DWORD PTR [ebp+3956]
	and edx, eax
	xor edx, DWORD PTR [ebp+3904]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3908]
	xor edx, DWORD PTR [ebp+3960]
	and edx, eax
	xor edx, DWORD PTR [ebp+3908]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3912]
	xor edx, DWORD PTR [ebp+3964]
	and edx, eax
	xor edx, DWORD PTR [ebp+3912]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3916]
	xor edx, DWORD PTR [ebp+3968]
	and edx, eax
	xor edx, DWORD PTR [ebp+3916]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3920]
	xor edx, DWORD PTR [ebp+3972]
	and edx, eax
	xor edx, DWORD PTR [ebp+3920]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3924]
	xor edx, DWORD PTR [ebp+3976]
	and edx, eax
	xor edx, DWORD PTR [ebp+3924]
	mov DWORD PTR [ecx+20], edx
	mov ebp, DWORD PTR [ebp+3992]
	ret
	.p2align 6
