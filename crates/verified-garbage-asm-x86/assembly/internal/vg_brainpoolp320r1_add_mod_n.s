// The functions of `src/internal/vg_brainpoolp320r1_add_mod_n.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_add_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3912], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	add eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3776], eax
	mov eax, DWORD PTR [ecx+4]
	adc eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3780], eax
	mov eax, DWORD PTR [ecx+8]
	adc eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3784], eax
	mov eax, DWORD PTR [ecx+12]
	adc eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3788], eax
	mov eax, DWORD PTR [ecx+16]
	adc eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3792], eax
	mov eax, DWORD PTR [ecx+20]
	adc eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3796], eax
	mov eax, DWORD PTR [ecx+24]
	adc eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3800], eax
	mov eax, DWORD PTR [ecx+28]
	adc eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3804], eax
	mov eax, DWORD PTR [ecx+32]
	adc eax, DWORD PTR [edx+32]
	mov DWORD PTR [ebp+3808], eax
	mov eax, DWORD PTR [ecx+36]
	adc eax, DWORD PTR [edx+36]
	mov DWORD PTR [ebp+3812], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3816], eax
	mov eax, DWORD PTR [ebp+3776]
	sub eax, 1153798929
	mov DWORD PTR [ebp+3860], eax
	mov eax, DWORD PTR [ebp+3780]
	sbb eax, -2037295781
	mov DWORD PTR [ebp+3864], eax
	mov eax, DWORD PTR [ebp+3784]
	sbb eax, -293185303
	mov DWORD PTR [ebp+3868], eax
	mov eax, DWORD PTR [ebp+3788]
	sbb eax, 759705287
	mov DWORD PTR [ebp+3872], eax
	mov eax, DWORD PTR [ebp+3792]
	sbb eax, -1232137565
	mov DWORD PTR [ebp+3876], eax
	mov eax, DWORD PTR [ebp+3796]
	sbb eax, -108015707
	mov DWORD PTR [ebp+3880], eax
	mov eax, DWORD PTR [ebp+3800]
	sbb eax, -771628955
	mov DWORD PTR [ebp+3884], eax
	mov eax, DWORD PTR [ebp+3804]
	sbb eax, -516130722
	mov DWORD PTR [ebp+3888], eax
	mov eax, DWORD PTR [ebp+3808]
	sbb eax, 918310839
	mov DWORD PTR [ebp+3892], eax
	mov eax, DWORD PTR [ebp+3812]
	sbb eax, -748796128
	mov DWORD PTR [ebp+3896], eax
	mov eax, DWORD PTR [ebp+3816]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3776]
	xor edx, DWORD PTR [ebp+3860]
	and edx, eax
	xor edx, DWORD PTR [ebp+3776]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3780]
	xor edx, DWORD PTR [ebp+3864]
	and edx, eax
	xor edx, DWORD PTR [ebp+3780]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3784]
	xor edx, DWORD PTR [ebp+3868]
	and edx, eax
	xor edx, DWORD PTR [ebp+3784]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3788]
	xor edx, DWORD PTR [ebp+3872]
	and edx, eax
	xor edx, DWORD PTR [ebp+3788]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3792]
	xor edx, DWORD PTR [ebp+3876]
	and edx, eax
	xor edx, DWORD PTR [ebp+3792]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3796]
	xor edx, DWORD PTR [ebp+3880]
	and edx, eax
	xor edx, DWORD PTR [ebp+3796]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3800]
	xor edx, DWORD PTR [ebp+3884]
	and edx, eax
	xor edx, DWORD PTR [ebp+3800]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3804]
	xor edx, DWORD PTR [ebp+3888]
	and edx, eax
	xor edx, DWORD PTR [ebp+3804]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3808]
	xor edx, DWORD PTR [ebp+3892]
	and edx, eax
	xor edx, DWORD PTR [ebp+3808]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3812]
	xor edx, DWORD PTR [ebp+3896]
	and edx, eax
	xor edx, DWORD PTR [ebp+3812]
	mov DWORD PTR [ecx+36], edx
	mov ebp, DWORD PTR [ebp+3912]
	ret
	.p2align 6
