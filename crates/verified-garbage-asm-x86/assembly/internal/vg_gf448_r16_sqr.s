// The functions of `src/internal/vg_gf448_r16_sqr.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_gf448_r16_sqr:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+4080], ebx
	mov DWORD PTR [eax+4084], esi
	mov DWORD PTR [eax+4088], edi
	mov DWORD PTR [eax+4092], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	add esi, edi
	mov eax, DWORD PTR [esi]
	mov edx, DWORD PTR [esi+4]
	ror edx, 16
	add eax, edx
	mov DWORD PTR [edi+3584], eax
	mov eax, DWORD PTR [esi+8]
	mov edx, DWORD PTR [esi+12]
	ror edx, 16
	add eax, edx
	mov DWORD PTR [edi+3588], eax
	mov eax, DWORD PTR [esi+16]
	mov edx, DWORD PTR [esi+20]
	ror edx, 16
	add eax, edx
	mov DWORD PTR [edi+3592], eax
	mov eax, DWORD PTR [esi+24]
	mov edx, DWORD PTR [esi+28]
	ror edx, 16
	add eax, edx
	mov DWORD PTR [edi+3596], eax
	mov eax, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+36]
	ror edx, 16
	add eax, edx
	mov DWORD PTR [edi+3600], eax
	mov eax, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+44]
	ror edx, 16
	add eax, edx
	mov DWORD PTR [edi+3604], eax
	mov eax, DWORD PTR [esi+48]
	mov edx, DWORD PTR [esi+52]
	ror edx, 16
	add eax, edx
	mov DWORD PTR [edi+3608], eax
	mov eax, DWORD PTR [esi+56]
	mov edx, DWORD PTR [esi+60]
	ror edx, 16
	add eax, edx
	mov DWORD PTR [edi+3612], eax
	mov eax, DWORD PTR [esi+64]
	mov edx, DWORD PTR [esi+68]
	ror edx, 16
	add eax, edx
	mov DWORD PTR [edi+3616], eax
	mov eax, DWORD PTR [esi+72]
	mov edx, DWORD PTR [esi+76]
	ror edx, 16
	add eax, edx
	mov DWORD PTR [edi+3620], eax
	mov eax, DWORD PTR [esi+80]
	mov edx, DWORD PTR [esi+84]
	ror edx, 16
	add eax, edx
	mov DWORD PTR [edi+3624], eax
	mov eax, DWORD PTR [esi+88]
	mov edx, DWORD PTR [esi+92]
	ror edx, 16
	add eax, edx
	mov DWORD PTR [edi+3628], eax
	mov eax, DWORD PTR [esi+96]
	mov edx, DWORD PTR [esi+100]
	ror edx, 16
	add eax, edx
	mov DWORD PTR [edi+3632], eax
	mov eax, DWORD PTR [esi+104]
	mov edx, DWORD PTR [esi+108]
	ror edx, 16
	add eax, edx
	mov DWORD PTR [edi+3636], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3696], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3700], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3592]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3588]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3704], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3596]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3592]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3708], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3600]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3596]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3592]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3712], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3604]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3600]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3596]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3716], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3608]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3604]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3600]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3596]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3720], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3612]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3608]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3604]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3600]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3724], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3616]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3612]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3608]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3604]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3600]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3728], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3620]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3616]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3612]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3608]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3604]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3732], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3624]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3620]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3616]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3612]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3608]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3604]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3736], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3628]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3624]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3620]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3616]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3612]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3608]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3740], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3632]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3628]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3624]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3620]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3616]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3612]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3608]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3744], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3632]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3628]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3624]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3620]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3616]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3612]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3748], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3632]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3628]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3624]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3620]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3616]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3612]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3752], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3632]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3628]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3624]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3620]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3616]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3756], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3632]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3628]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3624]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3620]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3616]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3760], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3632]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3628]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3624]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3620]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3764], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3632]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3628]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3624]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3620]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3768], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3632]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3628]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3624]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3772], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3632]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3628]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3624]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3776], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3632]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3628]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3780], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3632]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3628]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3784], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3632]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3788], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3632]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3792], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3796], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3800], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3804], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3696]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3752]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3780]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3840], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3700]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3756]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3784]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3844], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3704]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3760]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3788]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3848], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3708]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3764]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3792]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3852], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3712]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3768]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3796]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3856], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3716]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3772]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3800]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3860], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3720]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3776]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3804]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3724]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3780]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3752]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3780]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3728]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3784]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3756]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3784]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3732]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3788]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3760]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3788]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3736]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3792]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3764]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3792]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3740]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3796]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3768]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3796]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3744]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3800]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3772]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3800]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3748]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3804]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3776]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3804]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3896], ebx
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+3840]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3896]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3840], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3844]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3844], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3848]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3848], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3852]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3852], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3856]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3856], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3860]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3860], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3868]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3896]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3896], ebx
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	add ebx, DWORD PTR [edi+3840]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3896]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3840], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3844]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3844], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3848]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3848], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3852]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3852], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3856]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3856], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3860]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3860], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3864]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3864], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3868]
	adc ecx, 0
	adc ebp, 0
	add ebx, DWORD PTR [edi+3896]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3868], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3872]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3872], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3876]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3876], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3880]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3880], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3884]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3884], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3888]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3888], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	add ebx, DWORD PTR [edi+3892]
	adc ecx, 0
	adc ebp, 0
	mov DWORD PTR [edi+3892], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov ebp, DWORD PTR [esp+8]
	add ebp, edi
	mov eax, DWORD PTR [edi+3840]
	mov edx, eax
	and eax, 65535
	shr edx, 16
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], edx
	mov eax, DWORD PTR [edi+3844]
	mov edx, eax
	and eax, 65535
	shr edx, 16
	mov DWORD PTR [ebp+8], eax
	mov DWORD PTR [ebp+12], edx
	mov eax, DWORD PTR [edi+3848]
	mov edx, eax
	and eax, 65535
	shr edx, 16
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], edx
	mov eax, DWORD PTR [edi+3852]
	mov edx, eax
	and eax, 65535
	shr edx, 16
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+28], edx
	mov eax, DWORD PTR [edi+3856]
	mov edx, eax
	and eax, 65535
	shr edx, 16
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], edx
	mov eax, DWORD PTR [edi+3860]
	mov edx, eax
	and eax, 65535
	shr edx, 16
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], edx
	mov eax, DWORD PTR [edi+3864]
	mov edx, eax
	and eax, 65535
	shr edx, 16
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], edx
	mov eax, DWORD PTR [edi+3868]
	mov edx, eax
	and eax, 65535
	shr edx, 16
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], edx
	mov eax, DWORD PTR [edi+3872]
	mov edx, eax
	and eax, 65535
	shr edx, 16
	mov DWORD PTR [ebp+64], eax
	mov DWORD PTR [ebp+68], edx
	mov eax, DWORD PTR [edi+3876]
	mov edx, eax
	and eax, 65535
	shr edx, 16
	mov DWORD PTR [ebp+72], eax
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [edi+3880]
	mov edx, eax
	and eax, 65535
	shr edx, 16
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], edx
	mov eax, DWORD PTR [edi+3884]
	mov edx, eax
	and eax, 65535
	shr edx, 16
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], edx
	mov eax, DWORD PTR [edi+3888]
	mov edx, eax
	and eax, 65535
	shr edx, 16
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], edx
	mov eax, DWORD PTR [edi+3892]
	mov edx, eax
	and eax, 65535
	shr edx, 16
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], edx
	mov ebx, DWORD PTR [edi+4080]
	mov esi, DWORD PTR [edi+4084]
	mov ebp, DWORD PTR [edi+4092]
	mov edi, DWORD PTR [edi+4088]
	ret
	.p2align 6
