// The functions of `src/internal/vg_brainpoolp512r1_mul_mod_n.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
