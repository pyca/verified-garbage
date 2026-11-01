// The functions of `src/internal/vg_brainpoolp512r1_sub_mod_n.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_sub_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3792], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	sub eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3584], eax
	mov eax, DWORD PTR [ecx+4]
	sbb eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3588], eax
	mov eax, DWORD PTR [ecx+8]
	sbb eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3592], eax
	mov eax, DWORD PTR [ecx+12]
	sbb eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3596], eax
	mov eax, DWORD PTR [ecx+16]
	sbb eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3600], eax
	mov eax, DWORD PTR [ecx+20]
	sbb eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3604], eax
	mov eax, DWORD PTR [ecx+24]
	sbb eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3608], eax
	mov eax, DWORD PTR [ecx+28]
	sbb eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3612], eax
	mov eax, DWORD PTR [ecx+32]
	sbb eax, DWORD PTR [edx+32]
	mov DWORD PTR [ebp+3616], eax
	mov eax, DWORD PTR [ecx+36]
	sbb eax, DWORD PTR [edx+36]
	mov DWORD PTR [ebp+3620], eax
	mov eax, DWORD PTR [ecx+40]
	sbb eax, DWORD PTR [edx+40]
	mov DWORD PTR [ebp+3624], eax
	mov eax, DWORD PTR [ecx+44]
	sbb eax, DWORD PTR [edx+44]
	mov DWORD PTR [ebp+3628], eax
	mov eax, DWORD PTR [ecx+48]
	sbb eax, DWORD PTR [edx+48]
	mov DWORD PTR [ebp+3632], eax
	mov eax, DWORD PTR [ecx+52]
	sbb eax, DWORD PTR [edx+52]
	mov DWORD PTR [ebp+3636], eax
	mov eax, DWORD PTR [ecx+56]
	sbb eax, DWORD PTR [edx+56]
	mov DWORD PTR [ebp+3640], eax
	mov eax, DWORD PTR [ecx+60]
	sbb eax, DWORD PTR [edx+60]
	mov DWORD PTR [ebp+3644], eax
	sbb eax, eax
	mov edx, -1666645911
	and edx, eax
	mov DWORD PTR [ebp+3716], edx
	mov edx, -1249405310
	and edx, eax
	mov DWORD PTR [ebp+3720], edx
	mov edx, 140368605
	and edx, eax
	mov DWORD PTR [ebp+3724], edx
	mov edx, 498193281
	and edx, eax
	mov DWORD PTR [ebp+3728], edx
	mov edx, 2141982791
	and edx, eax
	mov DWORD PTR [ebp+3732], edx
	mov edx, 1099325721
	and edx, eax
	mov DWORD PTR [ebp+3736], edx
	mov edx, 1286153753
	and edx, eax
	mov DWORD PTR [ebp+3740], edx
	mov edx, 1430150209
	and edx, eax
	mov DWORD PTR [ebp+3744], edx
	mov edx, 1882392688
	and edx, eax
	mov DWORD PTR [ebp+3748], edx
	mov edx, -698114870
	and edx, eax
	mov DWORD PTR [ebp+3752], edx
	mov edx, -1278619122
	and edx, eax
	mov DWORD PTR [ebp+3756], edx
	mov edx, -886010445
	and edx, eax
	mov DWORD PTR [ebp+3760], edx
	mov edx, 868875271
	and edx, eax
	mov DWORD PTR [ebp+3764], edx
	mov edx, 1070917294
	and edx, eax
	mov DWORD PTR [ebp+3768], edx
	mov edx, -605436789
	and edx, eax
	mov DWORD PTR [ebp+3772], edx
	mov edx, -1428316744
	and edx, eax
	mov DWORD PTR [ebp+3776], edx
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3584]
	add edx, DWORD PTR [ebp+3716]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3588]
	adc edx, DWORD PTR [ebp+3720]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3592]
	adc edx, DWORD PTR [ebp+3724]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3596]
	adc edx, DWORD PTR [ebp+3728]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3600]
	adc edx, DWORD PTR [ebp+3732]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3604]
	adc edx, DWORD PTR [ebp+3736]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3608]
	adc edx, DWORD PTR [ebp+3740]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3612]
	adc edx, DWORD PTR [ebp+3744]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3616]
	adc edx, DWORD PTR [ebp+3748]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3620]
	adc edx, DWORD PTR [ebp+3752]
	mov DWORD PTR [ecx+36], edx
	mov edx, DWORD PTR [ebp+3624]
	adc edx, DWORD PTR [ebp+3756]
	mov DWORD PTR [ecx+40], edx
	mov edx, DWORD PTR [ebp+3628]
	adc edx, DWORD PTR [ebp+3760]
	mov DWORD PTR [ecx+44], edx
	mov edx, DWORD PTR [ebp+3632]
	adc edx, DWORD PTR [ebp+3764]
	mov DWORD PTR [ecx+48], edx
	mov edx, DWORD PTR [ebp+3636]
	adc edx, DWORD PTR [ebp+3768]
	mov DWORD PTR [ecx+52], edx
	mov edx, DWORD PTR [ebp+3640]
	adc edx, DWORD PTR [ebp+3772]
	mov DWORD PTR [ecx+56], edx
	mov edx, DWORD PTR [ebp+3644]
	adc edx, DWORD PTR [ebp+3776]
	mov DWORD PTR [ecx+60], edx
	mov ebp, DWORD PTR [ebp+3792]
	ret
	.p2align 6
