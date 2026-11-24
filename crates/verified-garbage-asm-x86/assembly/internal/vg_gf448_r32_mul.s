// The functions of `src/internal/vg_gf448_r32_mul.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_gf448_r32_mul:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+4080], ebx
	mov DWORD PTR [eax+4084], esi
	mov DWORD PTR [eax+4088], edi
	mov DWORD PTR [eax+4092], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	add esi, edi
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+3584], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+3588], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+3592], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+3596], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+3600], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+3604], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+3608], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+3612], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+3616], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+3620], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+3624], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+3628], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+3632], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+3636], eax
	mov esi, DWORD PTR [esp+16]
	add esi, edi
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+3640], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+3644], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+3648], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+3652], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+3656], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+3660], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+3664], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+3668], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+3672], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+3676], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+3680], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+3684], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+3688], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+3692], eax
	mov ebx, 0
	mov ecx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3696], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3700], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3704], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3708], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3712], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3716], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3720], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3724], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3728], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3732], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3736], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3740], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3744], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3584]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3640]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3748], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3588]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3644]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3752], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3592]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3648]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3756], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3596]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3652]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3760], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3600]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3656]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3764], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3604]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3660]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3768], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3608]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3664]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3772], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3612]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3668]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3776], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3616]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3672]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3780], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3620]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3676]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3784], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3624]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3680]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3788], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3628]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3684]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3792], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3632]
	mov edx, DWORD PTR [edi+3692]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3688]
	mul edx
	add ebx, eax
	adc ecx, edx
	adc ebp, 0
	mov DWORD PTR [edi+3796], ebx
	mov ebx, ecx
	mov ecx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+3636]
	mov edx, DWORD PTR [edi+3692]
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
	mov ebp, DWORD PTR [esp+8]
	add ebp, edi
	xor ecx, ecx
	mov eax, DWORD PTR [edi+3696]
	adc eax, DWORD PTR [edi+3752]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [edi+3700]
	adc eax, DWORD PTR [edi+3756]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [edi+3704]
	adc eax, DWORD PTR [edi+3760]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [edi+3708]
	adc eax, DWORD PTR [edi+3764]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [edi+3712]
	adc eax, DWORD PTR [edi+3768]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [edi+3716]
	adc eax, DWORD PTR [edi+3772]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [edi+3720]
	adc eax, DWORD PTR [edi+3776]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [edi+3724]
	adc eax, DWORD PTR [edi+3780]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [edi+3728]
	adc eax, DWORD PTR [edi+3784]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [edi+3732]
	adc eax, DWORD PTR [edi+3788]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [edi+3736]
	adc eax, DWORD PTR [edi+3792]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [edi+3740]
	adc eax, DWORD PTR [edi+3796]
	mov DWORD PTR [ebp+44], eax
	mov eax, DWORD PTR [edi+3744]
	adc eax, DWORD PTR [edi+3800]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [edi+3748]
	adc eax, DWORD PTR [edi+3804]
	mov DWORD PTR [ebp+52], eax
	adc ecx, 0
	mov eax, DWORD PTR [ebp]
	adc eax, DWORD PTR [edi+3780]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, DWORD PTR [edi+3784]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, DWORD PTR [edi+3788]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, DWORD PTR [edi+3792]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, DWORD PTR [edi+3796]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, DWORD PTR [edi+3800]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, DWORD PTR [edi+3804]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [edi+3780]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+32]
	adc eax, DWORD PTR [edi+3784]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	adc eax, DWORD PTR [edi+3788]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	adc eax, DWORD PTR [edi+3792]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	adc eax, DWORD PTR [edi+3796]
	mov DWORD PTR [ebp+44], eax
	mov eax, DWORD PTR [ebp+48]
	adc eax, DWORD PTR [edi+3800]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	adc eax, DWORD PTR [edi+3804]
	mov DWORD PTR [ebp+52], eax
	adc ecx, 0
	mov eax, DWORD PTR [ebp+28]
	adc eax, DWORD PTR [edi+3752]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+32]
	adc eax, DWORD PTR [edi+3756]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	adc eax, DWORD PTR [edi+3760]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	adc eax, DWORD PTR [edi+3764]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	adc eax, DWORD PTR [edi+3768]
	mov DWORD PTR [ebp+44], eax
	mov eax, DWORD PTR [ebp+48]
	adc eax, DWORD PTR [edi+3772]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	adc eax, DWORD PTR [edi+3776]
	mov DWORD PTR [ebp+52], eax
	adc ecx, 0
	mov eax, DWORD PTR [ebp]
	adc eax, ecx
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, 0
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, 0
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, 0
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, 0
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, 0
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, 0
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, ecx
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+32]
	adc eax, 0
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	adc eax, 0
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	adc eax, 0
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	adc eax, 0
	mov DWORD PTR [ebp+44], eax
	mov eax, DWORD PTR [ebp+48]
	adc eax, 0
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	adc eax, 0
	mov DWORD PTR [ebp+52], eax
	sbb ecx, ecx
	and ecx, 1
	mov eax, DWORD PTR [ebp]
	adc eax, ecx
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, 0
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, 0
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, 0
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, 0
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, 0
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, 0
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, ecx
	mov DWORD PTR [ebp+28], eax
	mov ebx, DWORD PTR [edi+4080]
	mov esi, DWORD PTR [edi+4084]
	mov ebp, DWORD PTR [edi+4092]
	mov edi, DWORD PTR [edi+4088]
	ret
	.p2align 6
