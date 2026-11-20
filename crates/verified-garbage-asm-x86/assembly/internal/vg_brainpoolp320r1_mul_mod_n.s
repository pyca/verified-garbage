// The functions of `src/internal/vg_brainpoolp320r1_mul_mod_n.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_mul_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3900], ebx
	mov DWORD PTR [eax+3904], esi
	mov DWORD PTR [eax+3908], edi
	mov DWORD PTR [eax+3912], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+16]
	add esi, ebp
	mov edi, DWORD PTR [esp+12]
	add edi, ebp
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	mul ecx
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov DWORD PTR [ebp+3816], ebx
	mov eax, 0
	mov DWORD PTR [ebp+3820], eax
	mov eax, DWORD PTR [ebp+3776]
	mov ecx, -60669425
	mul ecx
	mov ecx, eax
	mov eax, 1153798929
	mul ecx
	add eax, DWORD PTR [ebp+3776]
	adc edx, 0
	mov DWORD PTR [ebp+3776], eax
	mov ebx, edx
	mov eax, -2037295781
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, -293185303
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, 759705287
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, -1232137565
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, -108015707
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, -771628955
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, -516130722
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, 918310839
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, -748796128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3816]
	add eax, ebx
	mov DWORD PTR [ebp+3816], eax
	mov eax, DWORD PTR [ebp+3820]
	adc eax, 0
	mov DWORD PTR [ebp+3820], eax
	mov ecx, DWORD PTR [edi+4]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3820]
	add eax, ebx
	mov DWORD PTR [ebp+3820], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3824], eax
	mov eax, DWORD PTR [ebp+3780]
	mov ecx, -60669425
	mul ecx
	mov ecx, eax
	mov eax, 1153798929
	mul ecx
	add eax, DWORD PTR [ebp+3780]
	adc edx, 0
	mov DWORD PTR [ebp+3780], eax
	mov ebx, edx
	mov eax, -2037295781
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, -293185303
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, 759705287
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, -1232137565
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, -108015707
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, -771628955
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, -516130722
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, 918310839
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, -748796128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3820]
	add eax, ebx
	mov DWORD PTR [ebp+3820], eax
	mov eax, DWORD PTR [ebp+3824]
	adc eax, 0
	mov DWORD PTR [ebp+3824], eax
	mov ecx, DWORD PTR [edi+8]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3824]
	add eax, ebx
	mov DWORD PTR [ebp+3824], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3828], eax
	mov eax, DWORD PTR [ebp+3784]
	mov ecx, -60669425
	mul ecx
	mov ecx, eax
	mov eax, 1153798929
	mul ecx
	add eax, DWORD PTR [ebp+3784]
	adc edx, 0
	mov DWORD PTR [ebp+3784], eax
	mov ebx, edx
	mov eax, -2037295781
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, -293185303
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, 759705287
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, -1232137565
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, -108015707
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, -771628955
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, -516130722
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, 918310839
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, -748796128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3824]
	add eax, ebx
	mov DWORD PTR [ebp+3824], eax
	mov eax, DWORD PTR [ebp+3828]
	adc eax, 0
	mov DWORD PTR [ebp+3828], eax
	mov ecx, DWORD PTR [edi+12]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3824]
	adc edx, 0
	mov DWORD PTR [ebp+3824], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3828]
	add eax, ebx
	mov DWORD PTR [ebp+3828], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3832], eax
	mov eax, DWORD PTR [ebp+3788]
	mov ecx, -60669425
	mul ecx
	mov ecx, eax
	mov eax, 1153798929
	mul ecx
	add eax, DWORD PTR [ebp+3788]
	adc edx, 0
	mov DWORD PTR [ebp+3788], eax
	mov ebx, edx
	mov eax, -2037295781
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, -293185303
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, 759705287
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, -1232137565
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, -108015707
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, -771628955
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, -516130722
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, 918310839
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, -748796128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3824]
	adc edx, 0
	mov DWORD PTR [ebp+3824], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3828]
	add eax, ebx
	mov DWORD PTR [ebp+3828], eax
	mov eax, DWORD PTR [ebp+3832]
	adc eax, 0
	mov DWORD PTR [ebp+3832], eax
	mov ecx, DWORD PTR [edi+16]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3824]
	adc edx, 0
	mov DWORD PTR [ebp+3824], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3828]
	adc edx, 0
	mov DWORD PTR [ebp+3828], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3832]
	add eax, ebx
	mov DWORD PTR [ebp+3832], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3836], eax
	mov eax, DWORD PTR [ebp+3792]
	mov ecx, -60669425
	mul ecx
	mov ecx, eax
	mov eax, 1153798929
	mul ecx
	add eax, DWORD PTR [ebp+3792]
	adc edx, 0
	mov DWORD PTR [ebp+3792], eax
	mov ebx, edx
	mov eax, -2037295781
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, -293185303
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, 759705287
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, -1232137565
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, -108015707
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, -771628955
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, -516130722
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, 918310839
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3824]
	adc edx, 0
	mov DWORD PTR [ebp+3824], eax
	mov ebx, edx
	mov eax, -748796128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3828]
	adc edx, 0
	mov DWORD PTR [ebp+3828], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3832]
	add eax, ebx
	mov DWORD PTR [ebp+3832], eax
	mov eax, DWORD PTR [ebp+3836]
	adc eax, 0
	mov DWORD PTR [ebp+3836], eax
	mov ecx, DWORD PTR [edi+20]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3824]
	adc edx, 0
	mov DWORD PTR [ebp+3824], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3828]
	adc edx, 0
	mov DWORD PTR [ebp+3828], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3832]
	adc edx, 0
	mov DWORD PTR [ebp+3832], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3836]
	add eax, ebx
	mov DWORD PTR [ebp+3836], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [ebp+3796]
	mov ecx, -60669425
	mul ecx
	mov ecx, eax
	mov eax, 1153798929
	mul ecx
	add eax, DWORD PTR [ebp+3796]
	adc edx, 0
	mov DWORD PTR [ebp+3796], eax
	mov ebx, edx
	mov eax, -2037295781
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, -293185303
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, 759705287
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, -1232137565
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, -108015707
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, -771628955
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, -516130722
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3824]
	adc edx, 0
	mov DWORD PTR [ebp+3824], eax
	mov ebx, edx
	mov eax, 918310839
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3828]
	adc edx, 0
	mov DWORD PTR [ebp+3828], eax
	mov ebx, edx
	mov eax, -748796128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3832]
	adc edx, 0
	mov DWORD PTR [ebp+3832], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3836]
	add eax, ebx
	mov DWORD PTR [ebp+3836], eax
	mov eax, DWORD PTR [ebp+3840]
	adc eax, 0
	mov DWORD PTR [ebp+3840], eax
	mov ecx, DWORD PTR [edi+24]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3824]
	adc edx, 0
	mov DWORD PTR [ebp+3824], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3828]
	adc edx, 0
	mov DWORD PTR [ebp+3828], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3832]
	adc edx, 0
	mov DWORD PTR [ebp+3832], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3836]
	adc edx, 0
	mov DWORD PTR [ebp+3836], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3840]
	add eax, ebx
	mov DWORD PTR [ebp+3840], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [ebp+3800]
	mov ecx, -60669425
	mul ecx
	mov ecx, eax
	mov eax, 1153798929
	mul ecx
	add eax, DWORD PTR [ebp+3800]
	adc edx, 0
	mov DWORD PTR [ebp+3800], eax
	mov ebx, edx
	mov eax, -2037295781
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, -293185303
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, 759705287
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, -1232137565
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, -108015707
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, -771628955
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3824]
	adc edx, 0
	mov DWORD PTR [ebp+3824], eax
	mov ebx, edx
	mov eax, -516130722
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3828]
	adc edx, 0
	mov DWORD PTR [ebp+3828], eax
	mov ebx, edx
	mov eax, 918310839
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3832]
	adc edx, 0
	mov DWORD PTR [ebp+3832], eax
	mov ebx, edx
	mov eax, -748796128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3836]
	adc edx, 0
	mov DWORD PTR [ebp+3836], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3840]
	add eax, ebx
	mov DWORD PTR [ebp+3840], eax
	mov eax, DWORD PTR [ebp+3844]
	adc eax, 0
	mov DWORD PTR [ebp+3844], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3824]
	adc edx, 0
	mov DWORD PTR [ebp+3824], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3828]
	adc edx, 0
	mov DWORD PTR [ebp+3828], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3832]
	adc edx, 0
	mov DWORD PTR [ebp+3832], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3836]
	adc edx, 0
	mov DWORD PTR [ebp+3836], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3840]
	adc edx, 0
	mov DWORD PTR [ebp+3840], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3844]
	add eax, ebx
	mov DWORD PTR [ebp+3844], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [ebp+3804]
	mov ecx, -60669425
	mul ecx
	mov ecx, eax
	mov eax, 1153798929
	mul ecx
	add eax, DWORD PTR [ebp+3804]
	adc edx, 0
	mov DWORD PTR [ebp+3804], eax
	mov ebx, edx
	mov eax, -2037295781
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, -293185303
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, 759705287
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, -1232137565
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, -108015707
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3824]
	adc edx, 0
	mov DWORD PTR [ebp+3824], eax
	mov ebx, edx
	mov eax, -771628955
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3828]
	adc edx, 0
	mov DWORD PTR [ebp+3828], eax
	mov ebx, edx
	mov eax, -516130722
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3832]
	adc edx, 0
	mov DWORD PTR [ebp+3832], eax
	mov ebx, edx
	mov eax, 918310839
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3836]
	adc edx, 0
	mov DWORD PTR [ebp+3836], eax
	mov ebx, edx
	mov eax, -748796128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3840]
	adc edx, 0
	mov DWORD PTR [ebp+3840], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3844]
	add eax, ebx
	mov DWORD PTR [ebp+3844], eax
	mov eax, DWORD PTR [ebp+3848]
	adc eax, 0
	mov DWORD PTR [ebp+3848], eax
	mov ecx, DWORD PTR [edi+32]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3824]
	adc edx, 0
	mov DWORD PTR [ebp+3824], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3828]
	adc edx, 0
	mov DWORD PTR [ebp+3828], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3832]
	adc edx, 0
	mov DWORD PTR [ebp+3832], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3836]
	adc edx, 0
	mov DWORD PTR [ebp+3836], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3840]
	adc edx, 0
	mov DWORD PTR [ebp+3840], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3844]
	adc edx, 0
	mov DWORD PTR [ebp+3844], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3848]
	add eax, ebx
	mov DWORD PTR [ebp+3848], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [ebp+3808]
	mov ecx, -60669425
	mul ecx
	mov ecx, eax
	mov eax, 1153798929
	mul ecx
	add eax, DWORD PTR [ebp+3808]
	adc edx, 0
	mov DWORD PTR [ebp+3808], eax
	mov ebx, edx
	mov eax, -2037295781
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, -293185303
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, 759705287
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, -1232137565
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3824]
	adc edx, 0
	mov DWORD PTR [ebp+3824], eax
	mov ebx, edx
	mov eax, -108015707
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3828]
	adc edx, 0
	mov DWORD PTR [ebp+3828], eax
	mov ebx, edx
	mov eax, -771628955
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3832]
	adc edx, 0
	mov DWORD PTR [ebp+3832], eax
	mov ebx, edx
	mov eax, -516130722
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3836]
	adc edx, 0
	mov DWORD PTR [ebp+3836], eax
	mov ebx, edx
	mov eax, 918310839
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3840]
	adc edx, 0
	mov DWORD PTR [ebp+3840], eax
	mov ebx, edx
	mov eax, -748796128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3844]
	adc edx, 0
	mov DWORD PTR [ebp+3844], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3848]
	add eax, ebx
	mov DWORD PTR [ebp+3848], eax
	mov eax, DWORD PTR [ebp+3852]
	adc eax, 0
	mov DWORD PTR [ebp+3852], eax
	mov ecx, DWORD PTR [edi+36]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3824]
	adc edx, 0
	mov DWORD PTR [ebp+3824], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3828]
	adc edx, 0
	mov DWORD PTR [ebp+3828], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3832]
	adc edx, 0
	mov DWORD PTR [ebp+3832], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3836]
	adc edx, 0
	mov DWORD PTR [ebp+3836], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3840]
	adc edx, 0
	mov DWORD PTR [ebp+3840], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3844]
	adc edx, 0
	mov DWORD PTR [ebp+3844], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3848]
	adc edx, 0
	mov DWORD PTR [ebp+3848], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3852]
	add eax, ebx
	mov DWORD PTR [ebp+3852], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3856], eax
	mov eax, DWORD PTR [ebp+3812]
	mov ecx, -60669425
	mul ecx
	mov ecx, eax
	mov eax, 1153798929
	mul ecx
	add eax, DWORD PTR [ebp+3812]
	adc edx, 0
	mov DWORD PTR [ebp+3812], eax
	mov ebx, edx
	mov eax, -2037295781
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3816]
	adc edx, 0
	mov DWORD PTR [ebp+3816], eax
	mov ebx, edx
	mov eax, -293185303
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3820]
	adc edx, 0
	mov DWORD PTR [ebp+3820], eax
	mov ebx, edx
	mov eax, 759705287
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3824]
	adc edx, 0
	mov DWORD PTR [ebp+3824], eax
	mov ebx, edx
	mov eax, -1232137565
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3828]
	adc edx, 0
	mov DWORD PTR [ebp+3828], eax
	mov ebx, edx
	mov eax, -108015707
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3832]
	adc edx, 0
	mov DWORD PTR [ebp+3832], eax
	mov ebx, edx
	mov eax, -771628955
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3836]
	adc edx, 0
	mov DWORD PTR [ebp+3836], eax
	mov ebx, edx
	mov eax, -516130722
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3840]
	adc edx, 0
	mov DWORD PTR [ebp+3840], eax
	mov ebx, edx
	mov eax, 918310839
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3844]
	adc edx, 0
	mov DWORD PTR [ebp+3844], eax
	mov ebx, edx
	mov eax, -748796128
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3848]
	adc edx, 0
	mov DWORD PTR [ebp+3848], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3852]
	add eax, ebx
	mov DWORD PTR [ebp+3852], eax
	mov eax, DWORD PTR [ebp+3856]
	adc eax, 0
	mov DWORD PTR [ebp+3856], eax
	mov eax, DWORD PTR [ebp+3816]
	sub eax, 1153798929
	mov DWORD PTR [ebp+3860], eax
	mov eax, DWORD PTR [ebp+3820]
	sbb eax, -2037295781
	mov DWORD PTR [ebp+3864], eax
	mov eax, DWORD PTR [ebp+3824]
	sbb eax, -293185303
	mov DWORD PTR [ebp+3868], eax
	mov eax, DWORD PTR [ebp+3828]
	sbb eax, 759705287
	mov DWORD PTR [ebp+3872], eax
	mov eax, DWORD PTR [ebp+3832]
	sbb eax, -1232137565
	mov DWORD PTR [ebp+3876], eax
	mov eax, DWORD PTR [ebp+3836]
	sbb eax, -108015707
	mov DWORD PTR [ebp+3880], eax
	mov eax, DWORD PTR [ebp+3840]
	sbb eax, -771628955
	mov DWORD PTR [ebp+3884], eax
	mov eax, DWORD PTR [ebp+3844]
	sbb eax, -516130722
	mov DWORD PTR [ebp+3888], eax
	mov eax, DWORD PTR [ebp+3848]
	sbb eax, 918310839
	mov DWORD PTR [ebp+3892], eax
	mov eax, DWORD PTR [ebp+3852]
	sbb eax, -748796128
	mov DWORD PTR [ebp+3896], eax
	mov eax, DWORD PTR [ebp+3856]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov esi, DWORD PTR [ebp+3904]
	mov edi, DWORD PTR [ebp+3908]
	mov edx, DWORD PTR [ebp+3816]
	xor edx, DWORD PTR [ebp+3860]
	and edx, eax
	xor edx, DWORD PTR [ebp+3816]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3820]
	xor edx, DWORD PTR [ebp+3864]
	and edx, eax
	xor edx, DWORD PTR [ebp+3820]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3824]
	xor edx, DWORD PTR [ebp+3868]
	and edx, eax
	xor edx, DWORD PTR [ebp+3824]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3828]
	xor edx, DWORD PTR [ebp+3872]
	and edx, eax
	xor edx, DWORD PTR [ebp+3828]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3832]
	xor edx, DWORD PTR [ebp+3876]
	and edx, eax
	xor edx, DWORD PTR [ebp+3832]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3836]
	xor edx, DWORD PTR [ebp+3880]
	and edx, eax
	xor edx, DWORD PTR [ebp+3836]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3840]
	xor edx, DWORD PTR [ebp+3884]
	and edx, eax
	xor edx, DWORD PTR [ebp+3840]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3844]
	xor edx, DWORD PTR [ebp+3888]
	and edx, eax
	xor edx, DWORD PTR [ebp+3844]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3848]
	xor edx, DWORD PTR [ebp+3892]
	and edx, eax
	xor edx, DWORD PTR [ebp+3848]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3852]
	xor edx, DWORD PTR [ebp+3896]
	and edx, eax
	xor edx, DWORD PTR [ebp+3852]
	mov DWORD PTR [ecx+36], edx
	mov ebx, DWORD PTR [ebp+3900]
	mov ebp, DWORD PTR [ebp+3912]
	ret
	.p2align 6
