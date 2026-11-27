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
	cmp edi, esi
	je 20f
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp+3584], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [ebp+3588], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [ebp+3592], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [ebp+3596], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [ebp+3600], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [ebp+3604], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [ebp+3608], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [ebp+3612], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [ebp+3616], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [ebp+3620], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [ebp+3624], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [ebp+3628], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [ebp+3632], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [ebp+3636], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [ebp+3640], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [ebp+3644], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp+3716], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [ebp+3720], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [ebp+3724], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [ebp+3728], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [ebp+3732], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [ebp+3736], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [ebp+3740], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [ebp+3744], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [ebp+3748], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [ebp+3752], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [ebp+3756], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [ebp+3760], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [ebp+3764], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [ebp+3768], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [ebp+3772], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [ebp+3776], eax
	mov edi, ebp
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3648], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3652], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3656], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3660], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3664], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3668], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3672], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3676], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3680], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3684], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3688], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3692], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3696], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3700], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3704], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3716]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3708], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3720]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3648], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3724]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3652], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3728]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3656], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3732]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3660], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3736]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3664], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3740]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3668], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3744]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3672], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3748]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3676], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3752]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3680], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3756]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3684], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3760]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3688], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3764]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3692], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3768]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3696], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3772]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3700], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3776]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3704], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3708], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3712], ebx
	mov ebp, edi
	jmp 21f
20:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp+3584], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [ebp+3588], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [ebp+3592], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [ebp+3596], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [ebp+3600], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [ebp+3604], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [ebp+3608], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [ebp+3612], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [ebp+3616], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [ebp+3620], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [ebp+3624], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [ebp+3628], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [ebp+3632], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [ebp+3636], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [ebp+3640], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [ebp+3644], eax
	mov edi, ebp
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3584]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3648], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3652], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3656], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3660], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3664], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3668], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3672], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3676], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3680], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3684], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3688], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3692], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3696], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3700], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3704], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3648]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3652]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, ebx
	mov edx, 253456423
	mul edx
	mov DWORD PTR [edi+3708], eax
	mov edx, -1666645911
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3652]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3656]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, -1249405310
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3648], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3656]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3660]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 140368605
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3652], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3660]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3664]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 498193281
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3656], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3664]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3668]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 2141982791
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3660], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3668]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3672]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 1099325721
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3664], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3672]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3676]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 1286153753
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3668], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3676]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3680]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 1430150209
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3672], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3680]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3684]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 1882392688
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3676], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
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
	mov eax, DWORD PTR [edi+3684]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, -698114870
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3680], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3688]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, -1278619122
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3684], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3636]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3692]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, -886010445
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3688], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3696]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 868875271
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3692], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3700]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, 1070917294
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3696], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3640]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add eax, eax
	adc edx, edx
	adc ebp, 0
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3704]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, -605436789
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3700], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3644]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3708]
	mov edx, -1428316744
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3704], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3708], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov DWORD PTR [edi+3712], ebx
	mov ebp, edi
21:
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
