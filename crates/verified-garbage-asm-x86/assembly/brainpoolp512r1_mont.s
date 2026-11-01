// The functions of `src/brainpoolp512r1_mont.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_mul_mod_p:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3780], ebx
	mov DWORD PTR [eax+3784], esi
	mov DWORD PTR [eax+3788], edi
	mov DWORD PTR [eax+3792], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+16]
	add esi, ebp
	mov edi, DWORD PTR [esp+12]
	add edi, ebp
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	mul ecx
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov DWORD PTR [ebp+3648], ebx
	mov eax, 0
	mov DWORD PTR [ebp+3652], eax
	mov eax, DWORD PTR [ebp+3584]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3648]
	add eax, ebx
	mov DWORD PTR [ebp+3648], eax
	mov eax, DWORD PTR [ebp+3652]
	adc eax, 0
	mov DWORD PTR [ebp+3652], eax
	mov ecx, DWORD PTR [edi+4]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3652]
	add eax, ebx
	mov DWORD PTR [ebp+3652], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3656], eax
	mov eax, DWORD PTR [ebp+3588]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3652]
	add eax, ebx
	mov DWORD PTR [ebp+3652], eax
	mov eax, DWORD PTR [ebp+3656]
	adc eax, 0
	mov DWORD PTR [ebp+3656], eax
	mov ecx, DWORD PTR [edi+8]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3656]
	add eax, ebx
	mov DWORD PTR [ebp+3656], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3660], eax
	mov eax, DWORD PTR [ebp+3592]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3656]
	add eax, ebx
	mov DWORD PTR [ebp+3656], eax
	mov eax, DWORD PTR [ebp+3660]
	adc eax, 0
	mov DWORD PTR [ebp+3660], eax
	mov ecx, DWORD PTR [edi+12]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3660]
	add eax, ebx
	mov DWORD PTR [ebp+3660], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3664], eax
	mov eax, DWORD PTR [ebp+3596]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3660]
	add eax, ebx
	mov DWORD PTR [ebp+3660], eax
	mov eax, DWORD PTR [ebp+3664]
	adc eax, 0
	mov DWORD PTR [ebp+3664], eax
	mov ecx, DWORD PTR [edi+16]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3664]
	add eax, ebx
	mov DWORD PTR [ebp+3664], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3668], eax
	mov eax, DWORD PTR [ebp+3600]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3664]
	add eax, ebx
	mov DWORD PTR [ebp+3664], eax
	mov eax, DWORD PTR [ebp+3668]
	adc eax, 0
	mov DWORD PTR [ebp+3668], eax
	mov ecx, DWORD PTR [edi+20]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3668]
	add eax, ebx
	mov DWORD PTR [ebp+3668], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3672], eax
	mov eax, DWORD PTR [ebp+3604]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3668]
	add eax, ebx
	mov DWORD PTR [ebp+3668], eax
	mov eax, DWORD PTR [ebp+3672]
	adc eax, 0
	mov DWORD PTR [ebp+3672], eax
	mov ecx, DWORD PTR [edi+24]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3672]
	add eax, ebx
	mov DWORD PTR [ebp+3672], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3676], eax
	mov eax, DWORD PTR [ebp+3608]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3672]
	add eax, ebx
	mov DWORD PTR [ebp+3672], eax
	mov eax, DWORD PTR [ebp+3676]
	adc eax, 0
	mov DWORD PTR [ebp+3676], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3676]
	add eax, ebx
	mov DWORD PTR [ebp+3676], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3680], eax
	mov eax, DWORD PTR [ebp+3612]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3676]
	add eax, ebx
	mov DWORD PTR [ebp+3676], eax
	mov eax, DWORD PTR [ebp+3680]
	adc eax, 0
	mov DWORD PTR [ebp+3680], eax
	mov ecx, DWORD PTR [edi+32]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3680]
	add eax, ebx
	mov DWORD PTR [ebp+3680], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3684], eax
	mov eax, DWORD PTR [ebp+3616]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3680]
	add eax, ebx
	mov DWORD PTR [ebp+3680], eax
	mov eax, DWORD PTR [ebp+3684]
	adc eax, 0
	mov DWORD PTR [ebp+3684], eax
	mov ecx, DWORD PTR [edi+36]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3684]
	add eax, ebx
	mov DWORD PTR [ebp+3684], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3688], eax
	mov eax, DWORD PTR [ebp+3620]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3684]
	add eax, ebx
	mov DWORD PTR [ebp+3684], eax
	mov eax, DWORD PTR [ebp+3688]
	adc eax, 0
	mov DWORD PTR [ebp+3688], eax
	mov ecx, DWORD PTR [edi+40]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3688]
	add eax, ebx
	mov DWORD PTR [ebp+3688], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3692], eax
	mov eax, DWORD PTR [ebp+3624]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3688]
	add eax, ebx
	mov DWORD PTR [ebp+3688], eax
	mov eax, DWORD PTR [ebp+3692]
	adc eax, 0
	mov DWORD PTR [ebp+3692], eax
	mov ecx, DWORD PTR [edi+44]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3692]
	add eax, ebx
	mov DWORD PTR [ebp+3692], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3696], eax
	mov eax, DWORD PTR [ebp+3628]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3692]
	add eax, ebx
	mov DWORD PTR [ebp+3692], eax
	mov eax, DWORD PTR [ebp+3696]
	adc eax, 0
	mov DWORD PTR [ebp+3696], eax
	mov ecx, DWORD PTR [edi+48]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3696]
	add eax, ebx
	mov DWORD PTR [ebp+3696], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3700], eax
	mov eax, DWORD PTR [ebp+3632]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3696]
	add eax, ebx
	mov DWORD PTR [ebp+3696], eax
	mov eax, DWORD PTR [ebp+3700]
	adc eax, 0
	mov DWORD PTR [ebp+3700], eax
	mov ecx, DWORD PTR [edi+52]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3696]
	adc edx, 0
	mov DWORD PTR [ebp+3696], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3700]
	add eax, ebx
	mov DWORD PTR [ebp+3700], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3704], eax
	mov eax, DWORD PTR [ebp+3636]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3696]
	adc edx, 0
	mov DWORD PTR [ebp+3696], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3700]
	add eax, ebx
	mov DWORD PTR [ebp+3700], eax
	mov eax, DWORD PTR [ebp+3704]
	adc eax, 0
	mov DWORD PTR [ebp+3704], eax
	mov ecx, DWORD PTR [edi+56]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3696]
	adc edx, 0
	mov DWORD PTR [ebp+3696], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3700]
	adc edx, 0
	mov DWORD PTR [ebp+3700], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3704]
	add eax, ebx
	mov DWORD PTR [ebp+3704], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3708], eax
	mov eax, DWORD PTR [ebp+3640]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3696]
	adc edx, 0
	mov DWORD PTR [ebp+3696], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3700]
	adc edx, 0
	mov DWORD PTR [ebp+3700], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3704]
	add eax, ebx
	mov DWORD PTR [ebp+3704], eax
	mov eax, DWORD PTR [ebp+3708]
	adc eax, 0
	mov DWORD PTR [ebp+3708], eax
	mov ecx, DWORD PTR [edi+60]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3696]
	adc edx, 0
	mov DWORD PTR [ebp+3696], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3700]
	adc edx, 0
	mov DWORD PTR [ebp+3700], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3704]
	adc edx, 0
	mov DWORD PTR [ebp+3704], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3708]
	add eax, ebx
	mov DWORD PTR [ebp+3708], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3712], eax
	mov eax, DWORD PTR [ebp+3644]
	mov ecx, 2106191813
	mul ecx
	mov ecx, eax
	mov eax, 1480214771
	mul ecx
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 682254422
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 763545221
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, 679608111
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, -425492250
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, -1362255574
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, -1681495998
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, 2102237952
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, 1882392689
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3696]
	adc edx, 0
	mov DWORD PTR [ebp+3696], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3700]
	adc edx, 0
	mov DWORD PTR [ebp+3700], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3704]
	adc edx, 0
	mov DWORD PTR [ebp+3704], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3708]
	add eax, ebx
	mov DWORD PTR [ebp+3708], eax
	mov eax, DWORD PTR [ebp+3712]
	adc eax, 0
	mov DWORD PTR [ebp+3712], eax
	mov eax, DWORD PTR [ebp+3648]
	sub eax, 1480214771
	mov DWORD PTR [ebp+3716], eax
	mov eax, DWORD PTR [ebp+3652]
	sbb eax, 682254422
	mov DWORD PTR [ebp+3720], eax
	mov eax, DWORD PTR [ebp+3656]
	sbb eax, 763545221
	mov DWORD PTR [ebp+3724], eax
	mov eax, DWORD PTR [ebp+3660]
	sbb eax, 679608111
	mov DWORD PTR [ebp+3728], eax
	mov eax, DWORD PTR [ebp+3664]
	sbb eax, -425492250
	mov DWORD PTR [ebp+3732], eax
	mov eax, DWORD PTR [ebp+3668]
	sbb eax, -1362255574
	mov DWORD PTR [ebp+3736], eax
	mov eax, DWORD PTR [ebp+3672]
	sbb eax, -1681495998
	mov DWORD PTR [ebp+3740], eax
	mov eax, DWORD PTR [ebp+3676]
	sbb eax, 2102237952
	mov DWORD PTR [ebp+3744], eax
	mov eax, DWORD PTR [ebp+3680]
	sbb eax, 1882392689
	mov DWORD PTR [ebp+3748], eax
	mov eax, DWORD PTR [ebp+3684]
	sbb eax, -698114870
	mov DWORD PTR [ebp+3752], eax
	mov eax, DWORD PTR [ebp+3688]
	sbb eax, -1278619122
	mov DWORD PTR [ebp+3756], eax
	mov eax, DWORD PTR [ebp+3692]
	sbb eax, -886010445
	mov DWORD PTR [ebp+3760], eax
	mov eax, DWORD PTR [ebp+3696]
	sbb eax, 868875271
	mov DWORD PTR [ebp+3764], eax
	mov eax, DWORD PTR [ebp+3700]
	sbb eax, 1070917294
	mov DWORD PTR [ebp+3768], eax
	mov eax, DWORD PTR [ebp+3704]
	sbb eax, -605436789
	mov DWORD PTR [ebp+3772], eax
	mov eax, DWORD PTR [ebp+3708]
	sbb eax, -1428316744
	mov DWORD PTR [ebp+3776], eax
	mov eax, DWORD PTR [ebp+3712]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov esi, DWORD PTR [ebp+3784]
	mov edi, DWORD PTR [ebp+3788]
	mov edx, DWORD PTR [ebp+3648]
	xor edx, DWORD PTR [ebp+3716]
	and edx, eax
	xor edx, DWORD PTR [ebp+3648]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3652]
	xor edx, DWORD PTR [ebp+3720]
	and edx, eax
	xor edx, DWORD PTR [ebp+3652]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3656]
	xor edx, DWORD PTR [ebp+3724]
	and edx, eax
	xor edx, DWORD PTR [ebp+3656]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3660]
	xor edx, DWORD PTR [ebp+3728]
	and edx, eax
	xor edx, DWORD PTR [ebp+3660]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3664]
	xor edx, DWORD PTR [ebp+3732]
	and edx, eax
	xor edx, DWORD PTR [ebp+3664]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3668]
	xor edx, DWORD PTR [ebp+3736]
	and edx, eax
	xor edx, DWORD PTR [ebp+3668]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3672]
	xor edx, DWORD PTR [ebp+3740]
	and edx, eax
	xor edx, DWORD PTR [ebp+3672]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3676]
	xor edx, DWORD PTR [ebp+3744]
	and edx, eax
	xor edx, DWORD PTR [ebp+3676]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3680]
	xor edx, DWORD PTR [ebp+3748]
	and edx, eax
	xor edx, DWORD PTR [ebp+3680]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3684]
	xor edx, DWORD PTR [ebp+3752]
	and edx, eax
	xor edx, DWORD PTR [ebp+3684]
	mov DWORD PTR [ecx+36], edx
	mov edx, DWORD PTR [ebp+3688]
	xor edx, DWORD PTR [ebp+3756]
	and edx, eax
	xor edx, DWORD PTR [ebp+3688]
	mov DWORD PTR [ecx+40], edx
	mov edx, DWORD PTR [ebp+3692]
	xor edx, DWORD PTR [ebp+3760]
	and edx, eax
	xor edx, DWORD PTR [ebp+3692]
	mov DWORD PTR [ecx+44], edx
	mov edx, DWORD PTR [ebp+3696]
	xor edx, DWORD PTR [ebp+3764]
	and edx, eax
	xor edx, DWORD PTR [ebp+3696]
	mov DWORD PTR [ecx+48], edx
	mov edx, DWORD PTR [ebp+3700]
	xor edx, DWORD PTR [ebp+3768]
	and edx, eax
	xor edx, DWORD PTR [ebp+3700]
	mov DWORD PTR [ecx+52], edx
	mov edx, DWORD PTR [ebp+3704]
	xor edx, DWORD PTR [ebp+3772]
	and edx, eax
	xor edx, DWORD PTR [ebp+3704]
	mov DWORD PTR [ecx+56], edx
	mov edx, DWORD PTR [ebp+3708]
	xor edx, DWORD PTR [ebp+3776]
	and edx, eax
	xor edx, DWORD PTR [ebp+3708]
	mov DWORD PTR [ecx+60], edx
	mov ebx, DWORD PTR [ebp+3780]
	mov ebp, DWORD PTR [ebp+3792]
	ret
	.p2align 6

vg_brainpoolp512r1_add_mod_p:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3792], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	add eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3584], eax
	mov eax, DWORD PTR [ecx+4]
	adc eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3588], eax
	mov eax, DWORD PTR [ecx+8]
	adc eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3592], eax
	mov eax, DWORD PTR [ecx+12]
	adc eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3596], eax
	mov eax, DWORD PTR [ecx+16]
	adc eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3600], eax
	mov eax, DWORD PTR [ecx+20]
	adc eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3604], eax
	mov eax, DWORD PTR [ecx+24]
	adc eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3608], eax
	mov eax, DWORD PTR [ecx+28]
	adc eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3612], eax
	mov eax, DWORD PTR [ecx+32]
	adc eax, DWORD PTR [edx+32]
	mov DWORD PTR [ebp+3616], eax
	mov eax, DWORD PTR [ecx+36]
	adc eax, DWORD PTR [edx+36]
	mov DWORD PTR [ebp+3620], eax
	mov eax, DWORD PTR [ecx+40]
	adc eax, DWORD PTR [edx+40]
	mov DWORD PTR [ebp+3624], eax
	mov eax, DWORD PTR [ecx+44]
	adc eax, DWORD PTR [edx+44]
	mov DWORD PTR [ebp+3628], eax
	mov eax, DWORD PTR [ecx+48]
	adc eax, DWORD PTR [edx+48]
	mov DWORD PTR [ebp+3632], eax
	mov eax, DWORD PTR [ecx+52]
	adc eax, DWORD PTR [edx+52]
	mov DWORD PTR [ebp+3636], eax
	mov eax, DWORD PTR [ecx+56]
	adc eax, DWORD PTR [edx+56]
	mov DWORD PTR [ebp+3640], eax
	mov eax, DWORD PTR [ecx+60]
	adc eax, DWORD PTR [edx+60]
	mov DWORD PTR [ebp+3644], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3648], eax
	mov eax, DWORD PTR [ebp+3584]
	sub eax, 1480214771
	mov DWORD PTR [ebp+3716], eax
	mov eax, DWORD PTR [ebp+3588]
	sbb eax, 682254422
	mov DWORD PTR [ebp+3720], eax
	mov eax, DWORD PTR [ebp+3592]
	sbb eax, 763545221
	mov DWORD PTR [ebp+3724], eax
	mov eax, DWORD PTR [ebp+3596]
	sbb eax, 679608111
	mov DWORD PTR [ebp+3728], eax
	mov eax, DWORD PTR [ebp+3600]
	sbb eax, -425492250
	mov DWORD PTR [ebp+3732], eax
	mov eax, DWORD PTR [ebp+3604]
	sbb eax, -1362255574
	mov DWORD PTR [ebp+3736], eax
	mov eax, DWORD PTR [ebp+3608]
	sbb eax, -1681495998
	mov DWORD PTR [ebp+3740], eax
	mov eax, DWORD PTR [ebp+3612]
	sbb eax, 2102237952
	mov DWORD PTR [ebp+3744], eax
	mov eax, DWORD PTR [ebp+3616]
	sbb eax, 1882392689
	mov DWORD PTR [ebp+3748], eax
	mov eax, DWORD PTR [ebp+3620]
	sbb eax, -698114870
	mov DWORD PTR [ebp+3752], eax
	mov eax, DWORD PTR [ebp+3624]
	sbb eax, -1278619122
	mov DWORD PTR [ebp+3756], eax
	mov eax, DWORD PTR [ebp+3628]
	sbb eax, -886010445
	mov DWORD PTR [ebp+3760], eax
	mov eax, DWORD PTR [ebp+3632]
	sbb eax, 868875271
	mov DWORD PTR [ebp+3764], eax
	mov eax, DWORD PTR [ebp+3636]
	sbb eax, 1070917294
	mov DWORD PTR [ebp+3768], eax
	mov eax, DWORD PTR [ebp+3640]
	sbb eax, -605436789
	mov DWORD PTR [ebp+3772], eax
	mov eax, DWORD PTR [ebp+3644]
	sbb eax, -1428316744
	mov DWORD PTR [ebp+3776], eax
	mov eax, DWORD PTR [ebp+3648]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3584]
	xor edx, DWORD PTR [ebp+3716]
	and edx, eax
	xor edx, DWORD PTR [ebp+3584]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3588]
	xor edx, DWORD PTR [ebp+3720]
	and edx, eax
	xor edx, DWORD PTR [ebp+3588]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3592]
	xor edx, DWORD PTR [ebp+3724]
	and edx, eax
	xor edx, DWORD PTR [ebp+3592]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3596]
	xor edx, DWORD PTR [ebp+3728]
	and edx, eax
	xor edx, DWORD PTR [ebp+3596]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3600]
	xor edx, DWORD PTR [ebp+3732]
	and edx, eax
	xor edx, DWORD PTR [ebp+3600]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3604]
	xor edx, DWORD PTR [ebp+3736]
	and edx, eax
	xor edx, DWORD PTR [ebp+3604]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3608]
	xor edx, DWORD PTR [ebp+3740]
	and edx, eax
	xor edx, DWORD PTR [ebp+3608]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3612]
	xor edx, DWORD PTR [ebp+3744]
	and edx, eax
	xor edx, DWORD PTR [ebp+3612]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3616]
	xor edx, DWORD PTR [ebp+3748]
	and edx, eax
	xor edx, DWORD PTR [ebp+3616]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3620]
	xor edx, DWORD PTR [ebp+3752]
	and edx, eax
	xor edx, DWORD PTR [ebp+3620]
	mov DWORD PTR [ecx+36], edx
	mov edx, DWORD PTR [ebp+3624]
	xor edx, DWORD PTR [ebp+3756]
	and edx, eax
	xor edx, DWORD PTR [ebp+3624]
	mov DWORD PTR [ecx+40], edx
	mov edx, DWORD PTR [ebp+3628]
	xor edx, DWORD PTR [ebp+3760]
	and edx, eax
	xor edx, DWORD PTR [ebp+3628]
	mov DWORD PTR [ecx+44], edx
	mov edx, DWORD PTR [ebp+3632]
	xor edx, DWORD PTR [ebp+3764]
	and edx, eax
	xor edx, DWORD PTR [ebp+3632]
	mov DWORD PTR [ecx+48], edx
	mov edx, DWORD PTR [ebp+3636]
	xor edx, DWORD PTR [ebp+3768]
	and edx, eax
	xor edx, DWORD PTR [ebp+3636]
	mov DWORD PTR [ecx+52], edx
	mov edx, DWORD PTR [ebp+3640]
	xor edx, DWORD PTR [ebp+3772]
	and edx, eax
	xor edx, DWORD PTR [ebp+3640]
	mov DWORD PTR [ecx+56], edx
	mov edx, DWORD PTR [ebp+3644]
	xor edx, DWORD PTR [ebp+3776]
	and edx, eax
	xor edx, DWORD PTR [ebp+3644]
	mov DWORD PTR [ecx+60], edx
	mov ebp, DWORD PTR [ebp+3792]
	ret
	.p2align 6

vg_brainpoolp512r1_sub_mod_p:
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
	mov edx, 1480214771
	and edx, eax
	mov DWORD PTR [ebp+3716], edx
	mov edx, 682254422
	and edx, eax
	mov DWORD PTR [ebp+3720], edx
	mov edx, 763545221
	and edx, eax
	mov DWORD PTR [ebp+3724], edx
	mov edx, 679608111
	and edx, eax
	mov DWORD PTR [ebp+3728], edx
	mov edx, -425492250
	and edx, eax
	mov DWORD PTR [ebp+3732], edx
	mov edx, -1362255574
	and edx, eax
	mov DWORD PTR [ebp+3736], edx
	mov edx, -1681495998
	and edx, eax
	mov DWORD PTR [ebp+3740], edx
	mov edx, 2102237952
	and edx, eax
	mov DWORD PTR [ebp+3744], edx
	mov edx, 1882392689
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

vg_brainpoolp512r1_mul_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3780], ebx
	mov DWORD PTR [eax+3784], esi
	mov DWORD PTR [eax+3788], edi
	mov DWORD PTR [eax+3792], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+16]
	add esi, ebp
	mov edi, DWORD PTR [esp+12]
	add edi, ebp
	mov ecx, DWORD PTR [edi]
	mov eax, DWORD PTR [esi]
	mul ecx
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov DWORD PTR [ebp+3648], ebx
	mov eax, 0
	mov DWORD PTR [ebp+3652], eax
	mov eax, DWORD PTR [ebp+3584]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3584]
	adc edx, 0
	mov DWORD PTR [ebp+3584], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3648]
	add eax, ebx
	mov DWORD PTR [ebp+3648], eax
	mov eax, DWORD PTR [ebp+3652]
	adc eax, 0
	mov DWORD PTR [ebp+3652], eax
	mov ecx, DWORD PTR [edi+4]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3652]
	add eax, ebx
	mov DWORD PTR [ebp+3652], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3656], eax
	mov eax, DWORD PTR [ebp+3588]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3588]
	adc edx, 0
	mov DWORD PTR [ebp+3588], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3652]
	add eax, ebx
	mov DWORD PTR [ebp+3652], eax
	mov eax, DWORD PTR [ebp+3656]
	adc eax, 0
	mov DWORD PTR [ebp+3656], eax
	mov ecx, DWORD PTR [edi+8]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3656]
	add eax, ebx
	mov DWORD PTR [ebp+3656], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3660], eax
	mov eax, DWORD PTR [ebp+3592]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3592]
	adc edx, 0
	mov DWORD PTR [ebp+3592], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3656]
	add eax, ebx
	mov DWORD PTR [ebp+3656], eax
	mov eax, DWORD PTR [ebp+3660]
	adc eax, 0
	mov DWORD PTR [ebp+3660], eax
	mov ecx, DWORD PTR [edi+12]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3660]
	add eax, ebx
	mov DWORD PTR [ebp+3660], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3664], eax
	mov eax, DWORD PTR [ebp+3596]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3596]
	adc edx, 0
	mov DWORD PTR [ebp+3596], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3660]
	add eax, ebx
	mov DWORD PTR [ebp+3660], eax
	mov eax, DWORD PTR [ebp+3664]
	adc eax, 0
	mov DWORD PTR [ebp+3664], eax
	mov ecx, DWORD PTR [edi+16]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3664]
	add eax, ebx
	mov DWORD PTR [ebp+3664], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3668], eax
	mov eax, DWORD PTR [ebp+3600]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3600]
	adc edx, 0
	mov DWORD PTR [ebp+3600], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3664]
	add eax, ebx
	mov DWORD PTR [ebp+3664], eax
	mov eax, DWORD PTR [ebp+3668]
	adc eax, 0
	mov DWORD PTR [ebp+3668], eax
	mov ecx, DWORD PTR [edi+20]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3668]
	add eax, ebx
	mov DWORD PTR [ebp+3668], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3672], eax
	mov eax, DWORD PTR [ebp+3604]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3604]
	adc edx, 0
	mov DWORD PTR [ebp+3604], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3668]
	add eax, ebx
	mov DWORD PTR [ebp+3668], eax
	mov eax, DWORD PTR [ebp+3672]
	adc eax, 0
	mov DWORD PTR [ebp+3672], eax
	mov ecx, DWORD PTR [edi+24]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3672]
	add eax, ebx
	mov DWORD PTR [ebp+3672], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3676], eax
	mov eax, DWORD PTR [ebp+3608]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3608]
	adc edx, 0
	mov DWORD PTR [ebp+3608], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3672]
	add eax, ebx
	mov DWORD PTR [ebp+3672], eax
	mov eax, DWORD PTR [ebp+3676]
	adc eax, 0
	mov DWORD PTR [ebp+3676], eax
	mov ecx, DWORD PTR [edi+28]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3676]
	add eax, ebx
	mov DWORD PTR [ebp+3676], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3680], eax
	mov eax, DWORD PTR [ebp+3612]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3612]
	adc edx, 0
	mov DWORD PTR [ebp+3612], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3676]
	add eax, ebx
	mov DWORD PTR [ebp+3676], eax
	mov eax, DWORD PTR [ebp+3680]
	adc eax, 0
	mov DWORD PTR [ebp+3680], eax
	mov ecx, DWORD PTR [edi+32]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3680]
	add eax, ebx
	mov DWORD PTR [ebp+3680], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3684], eax
	mov eax, DWORD PTR [ebp+3616]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3616]
	adc edx, 0
	mov DWORD PTR [ebp+3616], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3680]
	add eax, ebx
	mov DWORD PTR [ebp+3680], eax
	mov eax, DWORD PTR [ebp+3684]
	adc eax, 0
	mov DWORD PTR [ebp+3684], eax
	mov ecx, DWORD PTR [edi+36]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3684]
	add eax, ebx
	mov DWORD PTR [ebp+3684], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3688], eax
	mov eax, DWORD PTR [ebp+3620]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3620]
	adc edx, 0
	mov DWORD PTR [ebp+3620], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3684]
	add eax, ebx
	mov DWORD PTR [ebp+3684], eax
	mov eax, DWORD PTR [ebp+3688]
	adc eax, 0
	mov DWORD PTR [ebp+3688], eax
	mov ecx, DWORD PTR [edi+40]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3688]
	add eax, ebx
	mov DWORD PTR [ebp+3688], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3692], eax
	mov eax, DWORD PTR [ebp+3624]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3624]
	adc edx, 0
	mov DWORD PTR [ebp+3624], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3688]
	add eax, ebx
	mov DWORD PTR [ebp+3688], eax
	mov eax, DWORD PTR [ebp+3692]
	adc eax, 0
	mov DWORD PTR [ebp+3692], eax
	mov ecx, DWORD PTR [edi+44]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3692]
	add eax, ebx
	mov DWORD PTR [ebp+3692], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3696], eax
	mov eax, DWORD PTR [ebp+3628]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3628]
	adc edx, 0
	mov DWORD PTR [ebp+3628], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3692]
	add eax, ebx
	mov DWORD PTR [ebp+3692], eax
	mov eax, DWORD PTR [ebp+3696]
	adc eax, 0
	mov DWORD PTR [ebp+3696], eax
	mov ecx, DWORD PTR [edi+48]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3696]
	add eax, ebx
	mov DWORD PTR [ebp+3696], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3700], eax
	mov eax, DWORD PTR [ebp+3632]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3632]
	adc edx, 0
	mov DWORD PTR [ebp+3632], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3696]
	add eax, ebx
	mov DWORD PTR [ebp+3696], eax
	mov eax, DWORD PTR [ebp+3700]
	adc eax, 0
	mov DWORD PTR [ebp+3700], eax
	mov ecx, DWORD PTR [edi+52]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3696]
	adc edx, 0
	mov DWORD PTR [ebp+3696], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3700]
	add eax, ebx
	mov DWORD PTR [ebp+3700], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3704], eax
	mov eax, DWORD PTR [ebp+3636]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3636]
	adc edx, 0
	mov DWORD PTR [ebp+3636], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3696]
	adc edx, 0
	mov DWORD PTR [ebp+3696], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3700]
	add eax, ebx
	mov DWORD PTR [ebp+3700], eax
	mov eax, DWORD PTR [ebp+3704]
	adc eax, 0
	mov DWORD PTR [ebp+3704], eax
	mov ecx, DWORD PTR [edi+56]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3696]
	adc edx, 0
	mov DWORD PTR [ebp+3696], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3700]
	adc edx, 0
	mov DWORD PTR [ebp+3700], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3704]
	add eax, ebx
	mov DWORD PTR [ebp+3704], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3708], eax
	mov eax, DWORD PTR [ebp+3640]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3640]
	adc edx, 0
	mov DWORD PTR [ebp+3640], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3696]
	adc edx, 0
	mov DWORD PTR [ebp+3696], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3700]
	adc edx, 0
	mov DWORD PTR [ebp+3700], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3704]
	add eax, ebx
	mov DWORD PTR [ebp+3704], eax
	mov eax, DWORD PTR [ebp+3708]
	adc eax, 0
	mov DWORD PTR [ebp+3708], eax
	mov ecx, DWORD PTR [edi+60]
	mov eax, DWORD PTR [esi]
	mul ecx
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+4]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+8]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+12]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+16]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+20]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+24]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+28]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+32]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+36]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+40]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+44]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+48]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+52]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3696]
	adc edx, 0
	mov DWORD PTR [ebp+3696], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+56]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3700]
	adc edx, 0
	mov DWORD PTR [ebp+3700], eax
	mov ebx, edx
	mov eax, DWORD PTR [esi+60]
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3704]
	adc edx, 0
	mov DWORD PTR [ebp+3704], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3708]
	add eax, ebx
	mov DWORD PTR [ebp+3708], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3712], eax
	mov eax, DWORD PTR [ebp+3644]
	mov ecx, 253456423
	mul ecx
	mov ecx, eax
	mov eax, -1666645911
	mul ecx
	add eax, DWORD PTR [ebp+3644]
	adc edx, 0
	mov DWORD PTR [ebp+3644], eax
	mov ebx, edx
	mov eax, -1249405310
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3648]
	adc edx, 0
	mov DWORD PTR [ebp+3648], eax
	mov ebx, edx
	mov eax, 140368605
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3652]
	adc edx, 0
	mov DWORD PTR [ebp+3652], eax
	mov ebx, edx
	mov eax, 498193281
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3656]
	adc edx, 0
	mov DWORD PTR [ebp+3656], eax
	mov ebx, edx
	mov eax, 2141982791
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3660]
	adc edx, 0
	mov DWORD PTR [ebp+3660], eax
	mov ebx, edx
	mov eax, 1099325721
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3664]
	adc edx, 0
	mov DWORD PTR [ebp+3664], eax
	mov ebx, edx
	mov eax, 1286153753
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3668]
	adc edx, 0
	mov DWORD PTR [ebp+3668], eax
	mov ebx, edx
	mov eax, 1430150209
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3672]
	adc edx, 0
	mov DWORD PTR [ebp+3672], eax
	mov ebx, edx
	mov eax, 1882392688
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3676]
	adc edx, 0
	mov DWORD PTR [ebp+3676], eax
	mov ebx, edx
	mov eax, -698114870
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3680]
	adc edx, 0
	mov DWORD PTR [ebp+3680], eax
	mov ebx, edx
	mov eax, -1278619122
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3684]
	adc edx, 0
	mov DWORD PTR [ebp+3684], eax
	mov ebx, edx
	mov eax, -886010445
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3688]
	adc edx, 0
	mov DWORD PTR [ebp+3688], eax
	mov ebx, edx
	mov eax, 868875271
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3692]
	adc edx, 0
	mov DWORD PTR [ebp+3692], eax
	mov ebx, edx
	mov eax, 1070917294
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3696]
	adc edx, 0
	mov DWORD PTR [ebp+3696], eax
	mov ebx, edx
	mov eax, -605436789
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3700]
	adc edx, 0
	mov DWORD PTR [ebp+3700], eax
	mov ebx, edx
	mov eax, -1428316744
	mul ecx
	add eax, ebx
	adc edx, 0
	add eax, DWORD PTR [ebp+3704]
	adc edx, 0
	mov DWORD PTR [ebp+3704], eax
	mov ebx, edx
	mov eax, DWORD PTR [ebp+3708]
	add eax, ebx
	mov DWORD PTR [ebp+3708], eax
	mov eax, DWORD PTR [ebp+3712]
	adc eax, 0
	mov DWORD PTR [ebp+3712], eax
	mov eax, DWORD PTR [ebp+3648]
	sub eax, -1666645911
	mov DWORD PTR [ebp+3716], eax
	mov eax, DWORD PTR [ebp+3652]
	sbb eax, -1249405310
	mov DWORD PTR [ebp+3720], eax
	mov eax, DWORD PTR [ebp+3656]
	sbb eax, 140368605
	mov DWORD PTR [ebp+3724], eax
	mov eax, DWORD PTR [ebp+3660]
	sbb eax, 498193281
	mov DWORD PTR [ebp+3728], eax
	mov eax, DWORD PTR [ebp+3664]
	sbb eax, 2141982791
	mov DWORD PTR [ebp+3732], eax
	mov eax, DWORD PTR [ebp+3668]
	sbb eax, 1099325721
	mov DWORD PTR [ebp+3736], eax
	mov eax, DWORD PTR [ebp+3672]
	sbb eax, 1286153753
	mov DWORD PTR [ebp+3740], eax
	mov eax, DWORD PTR [ebp+3676]
	sbb eax, 1430150209
	mov DWORD PTR [ebp+3744], eax
	mov eax, DWORD PTR [ebp+3680]
	sbb eax, 1882392688
	mov DWORD PTR [ebp+3748], eax
	mov eax, DWORD PTR [ebp+3684]
	sbb eax, -698114870
	mov DWORD PTR [ebp+3752], eax
	mov eax, DWORD PTR [ebp+3688]
	sbb eax, -1278619122
	mov DWORD PTR [ebp+3756], eax
	mov eax, DWORD PTR [ebp+3692]
	sbb eax, -886010445
	mov DWORD PTR [ebp+3760], eax
	mov eax, DWORD PTR [ebp+3696]
	sbb eax, 868875271
	mov DWORD PTR [ebp+3764], eax
	mov eax, DWORD PTR [ebp+3700]
	sbb eax, 1070917294
	mov DWORD PTR [ebp+3768], eax
	mov eax, DWORD PTR [ebp+3704]
	sbb eax, -605436789
	mov DWORD PTR [ebp+3772], eax
	mov eax, DWORD PTR [ebp+3708]
	sbb eax, -1428316744
	mov DWORD PTR [ebp+3776], eax
	mov eax, DWORD PTR [ebp+3712]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov esi, DWORD PTR [ebp+3784]
	mov edi, DWORD PTR [ebp+3788]
	mov edx, DWORD PTR [ebp+3648]
	xor edx, DWORD PTR [ebp+3716]
	and edx, eax
	xor edx, DWORD PTR [ebp+3648]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3652]
	xor edx, DWORD PTR [ebp+3720]
	and edx, eax
	xor edx, DWORD PTR [ebp+3652]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3656]
	xor edx, DWORD PTR [ebp+3724]
	and edx, eax
	xor edx, DWORD PTR [ebp+3656]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3660]
	xor edx, DWORD PTR [ebp+3728]
	and edx, eax
	xor edx, DWORD PTR [ebp+3660]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3664]
	xor edx, DWORD PTR [ebp+3732]
	and edx, eax
	xor edx, DWORD PTR [ebp+3664]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3668]
	xor edx, DWORD PTR [ebp+3736]
	and edx, eax
	xor edx, DWORD PTR [ebp+3668]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3672]
	xor edx, DWORD PTR [ebp+3740]
	and edx, eax
	xor edx, DWORD PTR [ebp+3672]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3676]
	xor edx, DWORD PTR [ebp+3744]
	and edx, eax
	xor edx, DWORD PTR [ebp+3676]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3680]
	xor edx, DWORD PTR [ebp+3748]
	and edx, eax
	xor edx, DWORD PTR [ebp+3680]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3684]
	xor edx, DWORD PTR [ebp+3752]
	and edx, eax
	xor edx, DWORD PTR [ebp+3684]
	mov DWORD PTR [ecx+36], edx
	mov edx, DWORD PTR [ebp+3688]
	xor edx, DWORD PTR [ebp+3756]
	and edx, eax
	xor edx, DWORD PTR [ebp+3688]
	mov DWORD PTR [ecx+40], edx
	mov edx, DWORD PTR [ebp+3692]
	xor edx, DWORD PTR [ebp+3760]
	and edx, eax
	xor edx, DWORD PTR [ebp+3692]
	mov DWORD PTR [ecx+44], edx
	mov edx, DWORD PTR [ebp+3696]
	xor edx, DWORD PTR [ebp+3764]
	and edx, eax
	xor edx, DWORD PTR [ebp+3696]
	mov DWORD PTR [ecx+48], edx
	mov edx, DWORD PTR [ebp+3700]
	xor edx, DWORD PTR [ebp+3768]
	and edx, eax
	xor edx, DWORD PTR [ebp+3700]
	mov DWORD PTR [ecx+52], edx
	mov edx, DWORD PTR [ebp+3704]
	xor edx, DWORD PTR [ebp+3772]
	and edx, eax
	xor edx, DWORD PTR [ebp+3704]
	mov DWORD PTR [ecx+56], edx
	mov edx, DWORD PTR [ebp+3708]
	xor edx, DWORD PTR [ebp+3776]
	and edx, eax
	xor edx, DWORD PTR [ebp+3708]
	mov DWORD PTR [ecx+60], edx
	mov ebx, DWORD PTR [ebp+3780]
	mov ebp, DWORD PTR [ebp+3792]
	ret
	.p2align 6

vg_brainpoolp512r1_add_mod_n:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3792], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebp
	mov edx, DWORD PTR [esp+16]
	add edx, ebp
	mov eax, DWORD PTR [ecx]
	add eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+3584], eax
	mov eax, DWORD PTR [ecx+4]
	adc eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+3588], eax
	mov eax, DWORD PTR [ecx+8]
	adc eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+3592], eax
	mov eax, DWORD PTR [ecx+12]
	adc eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+3596], eax
	mov eax, DWORD PTR [ecx+16]
	adc eax, DWORD PTR [edx+16]
	mov DWORD PTR [ebp+3600], eax
	mov eax, DWORD PTR [ecx+20]
	adc eax, DWORD PTR [edx+20]
	mov DWORD PTR [ebp+3604], eax
	mov eax, DWORD PTR [ecx+24]
	adc eax, DWORD PTR [edx+24]
	mov DWORD PTR [ebp+3608], eax
	mov eax, DWORD PTR [ecx+28]
	adc eax, DWORD PTR [edx+28]
	mov DWORD PTR [ebp+3612], eax
	mov eax, DWORD PTR [ecx+32]
	adc eax, DWORD PTR [edx+32]
	mov DWORD PTR [ebp+3616], eax
	mov eax, DWORD PTR [ecx+36]
	adc eax, DWORD PTR [edx+36]
	mov DWORD PTR [ebp+3620], eax
	mov eax, DWORD PTR [ecx+40]
	adc eax, DWORD PTR [edx+40]
	mov DWORD PTR [ebp+3624], eax
	mov eax, DWORD PTR [ecx+44]
	adc eax, DWORD PTR [edx+44]
	mov DWORD PTR [ebp+3628], eax
	mov eax, DWORD PTR [ecx+48]
	adc eax, DWORD PTR [edx+48]
	mov DWORD PTR [ebp+3632], eax
	mov eax, DWORD PTR [ecx+52]
	adc eax, DWORD PTR [edx+52]
	mov DWORD PTR [ebp+3636], eax
	mov eax, DWORD PTR [ecx+56]
	adc eax, DWORD PTR [edx+56]
	mov DWORD PTR [ebp+3640], eax
	mov eax, DWORD PTR [ecx+60]
	adc eax, DWORD PTR [edx+60]
	mov DWORD PTR [ebp+3644], eax
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+3648], eax
	mov eax, DWORD PTR [ebp+3584]
	sub eax, -1666645911
	mov DWORD PTR [ebp+3716], eax
	mov eax, DWORD PTR [ebp+3588]
	sbb eax, -1249405310
	mov DWORD PTR [ebp+3720], eax
	mov eax, DWORD PTR [ebp+3592]
	sbb eax, 140368605
	mov DWORD PTR [ebp+3724], eax
	mov eax, DWORD PTR [ebp+3596]
	sbb eax, 498193281
	mov DWORD PTR [ebp+3728], eax
	mov eax, DWORD PTR [ebp+3600]
	sbb eax, 2141982791
	mov DWORD PTR [ebp+3732], eax
	mov eax, DWORD PTR [ebp+3604]
	sbb eax, 1099325721
	mov DWORD PTR [ebp+3736], eax
	mov eax, DWORD PTR [ebp+3608]
	sbb eax, 1286153753
	mov DWORD PTR [ebp+3740], eax
	mov eax, DWORD PTR [ebp+3612]
	sbb eax, 1430150209
	mov DWORD PTR [ebp+3744], eax
	mov eax, DWORD PTR [ebp+3616]
	sbb eax, 1882392688
	mov DWORD PTR [ebp+3748], eax
	mov eax, DWORD PTR [ebp+3620]
	sbb eax, -698114870
	mov DWORD PTR [ebp+3752], eax
	mov eax, DWORD PTR [ebp+3624]
	sbb eax, -1278619122
	mov DWORD PTR [ebp+3756], eax
	mov eax, DWORD PTR [ebp+3628]
	sbb eax, -886010445
	mov DWORD PTR [ebp+3760], eax
	mov eax, DWORD PTR [ebp+3632]
	sbb eax, 868875271
	mov DWORD PTR [ebp+3764], eax
	mov eax, DWORD PTR [ebp+3636]
	sbb eax, 1070917294
	mov DWORD PTR [ebp+3768], eax
	mov eax, DWORD PTR [ebp+3640]
	sbb eax, -605436789
	mov DWORD PTR [ebp+3772], eax
	mov eax, DWORD PTR [ebp+3644]
	sbb eax, -1428316744
	mov DWORD PTR [ebp+3776], eax
	mov eax, DWORD PTR [ebp+3648]
	sbb eax, 0
	sbb eax, eax
	xor eax, -1
	mov ecx, DWORD PTR [esp+8]
	add ecx, ebp
	mov edx, DWORD PTR [ebp+3584]
	xor edx, DWORD PTR [ebp+3716]
	and edx, eax
	xor edx, DWORD PTR [ebp+3584]
	mov DWORD PTR [ecx], edx
	mov edx, DWORD PTR [ebp+3588]
	xor edx, DWORD PTR [ebp+3720]
	and edx, eax
	xor edx, DWORD PTR [ebp+3588]
	mov DWORD PTR [ecx+4], edx
	mov edx, DWORD PTR [ebp+3592]
	xor edx, DWORD PTR [ebp+3724]
	and edx, eax
	xor edx, DWORD PTR [ebp+3592]
	mov DWORD PTR [ecx+8], edx
	mov edx, DWORD PTR [ebp+3596]
	xor edx, DWORD PTR [ebp+3728]
	and edx, eax
	xor edx, DWORD PTR [ebp+3596]
	mov DWORD PTR [ecx+12], edx
	mov edx, DWORD PTR [ebp+3600]
	xor edx, DWORD PTR [ebp+3732]
	and edx, eax
	xor edx, DWORD PTR [ebp+3600]
	mov DWORD PTR [ecx+16], edx
	mov edx, DWORD PTR [ebp+3604]
	xor edx, DWORD PTR [ebp+3736]
	and edx, eax
	xor edx, DWORD PTR [ebp+3604]
	mov DWORD PTR [ecx+20], edx
	mov edx, DWORD PTR [ebp+3608]
	xor edx, DWORD PTR [ebp+3740]
	and edx, eax
	xor edx, DWORD PTR [ebp+3608]
	mov DWORD PTR [ecx+24], edx
	mov edx, DWORD PTR [ebp+3612]
	xor edx, DWORD PTR [ebp+3744]
	and edx, eax
	xor edx, DWORD PTR [ebp+3612]
	mov DWORD PTR [ecx+28], edx
	mov edx, DWORD PTR [ebp+3616]
	xor edx, DWORD PTR [ebp+3748]
	and edx, eax
	xor edx, DWORD PTR [ebp+3616]
	mov DWORD PTR [ecx+32], edx
	mov edx, DWORD PTR [ebp+3620]
	xor edx, DWORD PTR [ebp+3752]
	and edx, eax
	xor edx, DWORD PTR [ebp+3620]
	mov DWORD PTR [ecx+36], edx
	mov edx, DWORD PTR [ebp+3624]
	xor edx, DWORD PTR [ebp+3756]
	and edx, eax
	xor edx, DWORD PTR [ebp+3624]
	mov DWORD PTR [ecx+40], edx
	mov edx, DWORD PTR [ebp+3628]
	xor edx, DWORD PTR [ebp+3760]
	and edx, eax
	xor edx, DWORD PTR [ebp+3628]
	mov DWORD PTR [ecx+44], edx
	mov edx, DWORD PTR [ebp+3632]
	xor edx, DWORD PTR [ebp+3764]
	and edx, eax
	xor edx, DWORD PTR [ebp+3632]
	mov DWORD PTR [ecx+48], edx
	mov edx, DWORD PTR [ebp+3636]
	xor edx, DWORD PTR [ebp+3768]
	and edx, eax
	xor edx, DWORD PTR [ebp+3636]
	mov DWORD PTR [ecx+52], edx
	mov edx, DWORD PTR [ebp+3640]
	xor edx, DWORD PTR [ebp+3772]
	and edx, eax
	xor edx, DWORD PTR [ebp+3640]
	mov DWORD PTR [ecx+56], edx
	mov edx, DWORD PTR [ebp+3644]
	xor edx, DWORD PTR [ebp+3776]
	and edx, eax
	xor edx, DWORD PTR [ebp+3644]
	mov DWORD PTR [ecx+60], edx
	mov ebp, DWORD PTR [ebp+3792]
	ret
	.p2align 6

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
