// The functions of `src/internal/vg_brainpoolp320r1_sub_mod_n.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_sub_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3912], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	sub eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3776], eax
	mov eax, DWORD PTR [ecx+4]
	sbb eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3780], eax
	mov eax, DWORD PTR [ecx+8]
	sbb eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3784], eax
	mov eax, DWORD PTR [ecx+12]
	sbb eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3788], eax
	mov eax, DWORD PTR [ecx+16]
	sbb eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3792], eax
	mov eax, DWORD PTR [ecx+20]
	sbb eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3796], eax
	mov eax, DWORD PTR [ecx+24]
	sbb eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3800], eax
	mov eax, DWORD PTR [ecx+28]
	sbb eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3804], eax
	mov eax, DWORD PTR [ecx+32]
	sbb eax, DWORD PTR [edx+32]
	mov DWORD PTR [ebp+3808], eax
	mov eax, DWORD PTR [ecx+36]
	sbb eax, DWORD PTR [edx+36]
	mov DWORD PTR [ebp+3812], eax
	sbb eax, eax
	mov edx, 1153798929
	and edx, eax
	mov DWORD PTR [ebp+3860], edx
	mov edx, -2037295781
	and edx, eax
	mov DWORD PTR [ebp+3864], edx
	mov edx, -293185303
	and edx, eax
	mov DWORD PTR [ebp+3868], edx
	mov edx, 759705287
	and edx, eax
	mov DWORD PTR [ebp+3872], edx
	mov edx, -1232137565
	and edx, eax
	mov DWORD PTR [ebp+3876], edx
	mov edx, -108015707
	and edx, eax
	mov DWORD PTR [ebp+3880], edx
	mov edx, -771628955
	and edx, eax
	mov DWORD PTR [ebp+3884], edx
	mov edx, -516130722
	and edx, eax
	mov DWORD PTR [ebp+3888], edx
	mov edx, 918310839
	and edx, eax
	mov DWORD PTR [ebp+3892], edx
	mov edx, -748796128
	and edx, eax
	mov DWORD PTR [ebp+3896], edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3776]
	add edx, DWORD PTR [ebp+3860]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3780]
	adc edx, DWORD PTR [ebp+3864]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3784]
	adc edx, DWORD PTR [ebp+3868]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3788]
	adc edx, DWORD PTR [ebp+3872]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3792]
	adc edx, DWORD PTR [ebp+3876]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3796]
	adc edx, DWORD PTR [ebp+3880]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3800]
	adc edx, DWORD PTR [ebp+3884]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3804]
	adc edx, DWORD PTR [ebp+3888]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3808]
	adc edx, DWORD PTR [ebp+3892]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3812]
	adc edx, DWORD PTR [ebp+3896]
	mov DWORD PTR [ecx+36], edx
	mov ebp, DWORD PTR [ebp+3912]
	ret
	.p2align 6
