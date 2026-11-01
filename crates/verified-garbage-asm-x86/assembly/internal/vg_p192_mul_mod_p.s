// The functions of `src/internal/vg_p192_mul_mod_p.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_mul_mod_p:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3980], ebx
	mov DWORD PTR [eax+3984], esi
	mov DWORD PTR [eax+3988], edi
	mov DWORD PTR [eax+3992], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+16]
	add esi, ebp
	mov edi, DWORD PTR [esp+12]
	add edi, ebp
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	mul ecx
	mov DWORD PTR [ebp+3904], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3908], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3912], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3916], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3920], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3924], eax
	mov ebx, edx
	mov DWORD PTR [ebp+3928], ebx
	mov eax, 0
	mov DWORD PTR [ebp+3932], eax
	mov ecx, DWORD PTR [ebp+3904]
	mov eax, -1
	mul ecx
	add eax, DWORD PTR [ebp+3904]
	adc edx, 0
	mov DWORD PTR [ebp+3904], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3908]
	adc edx, 0
	mov DWORD PTR [ebp+3908], eax
	mov ebx, edx
	mov eax, -2
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3912]
	adc edx, 0
	mov DWORD PTR [ebp+3912], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3916]
	adc edx, 0
	mov DWORD PTR [ebp+3916], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3920]
	adc edx, 0
	mov DWORD PTR [ebp+3920], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3924]
	adc edx, 0
	mov DWORD PTR [ebp+3924], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3928]
	add eax, ebx
	mov DWORD PTR [ebp+3928], eax
	mov eax, DWORD PTR [ebp+3932]
	adc eax, 0
	mov DWORD PTR [ebp+3932], eax
	mov ecx, DWORD PTR [edi+4]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3908]
	adc edx, 0
	mov DWORD PTR [ebp+3908], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3912]
	adc edx, 0
	mov DWORD PTR [ebp+3912], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3916]
	adc edx, 0
	mov DWORD PTR [ebp+3916], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3920]
	adc edx, 0
	mov DWORD PTR [ebp+3920], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3924]
	adc edx, 0
	mov DWORD PTR [ebp+3924], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3928]
	adc edx, 0
	mov DWORD PTR [ebp+3928], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3932]
	add eax, ebx
	mov DWORD PTR [ebp+3932], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3936], eax
	mov ecx, DWORD PTR [ebp+3908]
	mov eax, -1
	mul ecx
	add eax, DWORD PTR [ebp+3908]
	adc edx, 0
	mov DWORD PTR [ebp+3908], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3912]
	adc edx, 0
	mov DWORD PTR [ebp+3912], eax
	mov ebx, edx
	mov eax, -2
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3916]
	adc edx, 0
	mov DWORD PTR [ebp+3916], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3920]
	adc edx, 0
	mov DWORD PTR [ebp+3920], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3924]
	adc edx, 0
	mov DWORD PTR [ebp+3924], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3928]
	adc edx, 0
	mov DWORD PTR [ebp+3928], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3932]
	add eax, ebx
	mov DWORD PTR [ebp+3932], eax
	mov eax, DWORD PTR [ebp+3936]
	adc eax, 0
	mov DWORD PTR [ebp+3936], eax
	mov ecx, DWORD PTR [edi+8]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3912]
	adc edx, 0
	mov DWORD PTR [ebp+3912], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3916]
	adc edx, 0
	mov DWORD PTR [ebp+3916], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3920]
	adc edx, 0
	mov DWORD PTR [ebp+3920], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3924]
	adc edx, 0
	mov DWORD PTR [ebp+3924], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3928]
	adc edx, 0
	mov DWORD PTR [ebp+3928], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3932]
	adc edx, 0
	mov DWORD PTR [ebp+3932], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3936]
	add eax, ebx
	mov DWORD PTR [ebp+3936], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3940], eax
	mov ecx, DWORD PTR [ebp+3912]
	mov eax, -1
	mul ecx
	add eax, DWORD PTR [ebp+3912]
	adc edx, 0
	mov DWORD PTR [ebp+3912], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3916]
	adc edx, 0
	mov DWORD PTR [ebp+3916], eax
	mov ebx, edx
	mov eax, -2
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3920]
	adc edx, 0
	mov DWORD PTR [ebp+3920], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3924]
	adc edx, 0
	mov DWORD PTR [ebp+3924], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3928]
	adc edx, 0
	mov DWORD PTR [ebp+3928], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3932]
	adc edx, 0
	mov DWORD PTR [ebp+3932], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3936]
	add eax, ebx
	mov DWORD PTR [ebp+3936], eax
	mov eax, DWORD PTR [ebp+3940]
	adc eax, 0
	mov DWORD PTR [ebp+3940], eax
	mov ecx, DWORD PTR [edi+12]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3916]
	adc edx, 0
	mov DWORD PTR [ebp+3916], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3920]
	adc edx, 0
	mov DWORD PTR [ebp+3920], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3924]
	adc edx, 0
	mov DWORD PTR [ebp+3924], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3928]
	adc edx, 0
	mov DWORD PTR [ebp+3928], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3932]
	adc edx, 0
	mov DWORD PTR [ebp+3932], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3936]
	adc edx, 0
	mov DWORD PTR [ebp+3936], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3940]
	add eax, ebx
	mov DWORD PTR [ebp+3940], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3944], eax
	mov ecx, DWORD PTR [ebp+3916]
	mov eax, -1
	mul ecx
	add eax, DWORD PTR [ebp+3916]
	adc edx, 0
	mov DWORD PTR [ebp+3916], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3920]
	adc edx, 0
	mov DWORD PTR [ebp+3920], eax
	mov ebx, edx
	mov eax, -2
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3924]
	adc edx, 0
	mov DWORD PTR [ebp+3924], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3928]
	adc edx, 0
	mov DWORD PTR [ebp+3928], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3932]
	adc edx, 0
	mov DWORD PTR [ebp+3932], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3936]
	adc edx, 0
	mov DWORD PTR [ebp+3936], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3940]
	add eax, ebx
	mov DWORD PTR [ebp+3940], eax
	mov eax, DWORD PTR [ebp+3944]
	adc eax, 0
	mov DWORD PTR [ebp+3944], eax
	mov ecx, DWORD PTR [edi+16]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3920]
	adc edx, 0
	mov DWORD PTR [ebp+3920], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3924]
	adc edx, 0
	mov DWORD PTR [ebp+3924], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3928]
	adc edx, 0
	mov DWORD PTR [ebp+3928], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3932]
	adc edx, 0
	mov DWORD PTR [ebp+3932], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3936]
	adc edx, 0
	mov DWORD PTR [ebp+3936], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3940]
	adc edx, 0
	mov DWORD PTR [ebp+3940], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3944]
	add eax, ebx
	mov DWORD PTR [ebp+3944], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3948], eax
	mov ecx, DWORD PTR [ebp+3920]
	mov eax, -1
	mul ecx
	add eax, DWORD PTR [ebp+3920]
	adc edx, 0
	mov DWORD PTR [ebp+3920], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3924]
	adc edx, 0
	mov DWORD PTR [ebp+3924], eax
	mov ebx, edx
	mov eax, -2
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3928]
	adc edx, 0
	mov DWORD PTR [ebp+3928], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3932]
	adc edx, 0
	mov DWORD PTR [ebp+3932], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3936]
	adc edx, 0
	mov DWORD PTR [ebp+3936], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3940]
	adc edx, 0
	mov DWORD PTR [ebp+3940], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3944]
	add eax, ebx
	mov DWORD PTR [ebp+3944], eax
	mov eax, DWORD PTR [ebp+3948]
	adc eax, 0
	mov DWORD PTR [ebp+3948], eax
	mov ecx, DWORD PTR [edi+20]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3924]
	adc edx, 0
	mov DWORD PTR [ebp+3924], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3928]
	adc edx, 0
	mov DWORD PTR [ebp+3928], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3932]
	adc edx, 0
	mov DWORD PTR [ebp+3932], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3936]
	adc edx, 0
	mov DWORD PTR [ebp+3936], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3940]
	adc edx, 0
	mov DWORD PTR [ebp+3940], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3944]
	adc edx, 0
	mov DWORD PTR [ebp+3944], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3948]
	add eax, ebx
	mov DWORD PTR [ebp+3948], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3952], eax
	mov ecx, DWORD PTR [ebp+3924]
	mov eax, -1
	mul ecx
	add eax, DWORD PTR [ebp+3924]
	adc edx, 0
	mov DWORD PTR [ebp+3924], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3928]
	adc edx, 0
	mov DWORD PTR [ebp+3928], eax
	mov ebx, edx
	mov eax, -2
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3932]
	adc edx, 0
	mov DWORD PTR [ebp+3932], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3936]
	adc edx, 0
	mov DWORD PTR [ebp+3936], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3940]
	adc edx, 0
	mov DWORD PTR [ebp+3940], eax
	mov ebx, edx
	mov eax, -1
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3944]
	adc edx, 0
	mov DWORD PTR [ebp+3944], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3948]
	add eax, ebx
	mov DWORD PTR [ebp+3948], eax
	mov eax, DWORD PTR [ebp+3952]
	adc eax, 0
	mov DWORD PTR [ebp+3952], eax
	mov eax, DWORD PTR [ebp+3928]
	sub eax, -1
	mov DWORD PTR [ebp+3956], eax
	mov eax, DWORD PTR [ebp+3932]
	sbb eax, -1
	mov DWORD PTR [ebp+3960], eax
	mov eax, DWORD PTR [ebp+3936]
	sbb eax, -2
	mov DWORD PTR [ebp+3964], eax
	mov eax, DWORD PTR [ebp+3940]
	sbb eax, -1
	mov DWORD PTR [ebp+3968], eax
	mov eax, DWORD PTR [ebp+3944]
	sbb eax, -1
	mov DWORD PTR [ebp+3972], eax
	mov eax, DWORD PTR [ebp+3948]
	sbb eax, -1
	mov DWORD PTR [ebp+3976], eax
	mov eax, DWORD PTR [ebp+3952]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov esi, DWORD PTR [ebp+3984]
	mov edi, DWORD PTR [ebp+3988]
	mov edx, DWORD PTR [ebp+3928]
	xor edx, DWORD PTR [ebp+3956]
	and edx, eax
	xor edx, DWORD PTR [ebp+3928]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3932]
	xor edx, DWORD PTR [ebp+3960]
	and edx, eax
	xor edx, DWORD PTR [ebp+3932]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3936]
	xor edx, DWORD PTR [ebp+3964]
	and edx, eax
	xor edx, DWORD PTR [ebp+3936]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3940]
	xor edx, DWORD PTR [ebp+3968]
	and edx, eax
	xor edx, DWORD PTR [ebp+3940]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3944]
	xor edx, DWORD PTR [ebp+3972]
	and edx, eax
	xor edx, DWORD PTR [ebp+3944]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3948]
	xor edx, DWORD PTR [ebp+3976]
	and edx, eax
	xor edx, DWORD PTR [ebp+3948]
	mov DWORD PTR [ecx+20], edx
	mov ebx, DWORD PTR [ebp+3980]
	mov ebp, DWORD PTR [ebp+3992]
	ret
	.p2align 6
