// The functions of `src/internal/vg_ecdsa_p521_sign_scalar.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p521_sign_scalar:
	call {vg_p521_inv_mod_n}
	mov r12, rsi
	mov esi, 2800
	mov edx, 2656
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2872
	mov edx, 2368
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2944
	mov edx, 2440
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3016
	mov edx, 2800
	mov ecx, 2872
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r9d, 0
	mov r8, QWORD PTR [rdi+3016]
	add r8, QWORD PTR [rdi+2944]
	mov QWORD PTR [rdi+4024], r8
	mov r8, QWORD PTR [rdi+3024]
	adc r8, QWORD PTR [rdi+2952]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+3032]
	adc r8, QWORD PTR [rdi+2960]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+3040]
	adc r8, QWORD PTR [rdi+2968]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+3048]
	adc r8, QWORD PTR [rdi+2976]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+3056]
	adc r8, QWORD PTR [rdi+2984]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+3064]
	adc r8, QWORD PTR [rdi+2992]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+3072]
	adc r8, QWORD PTR [rdi+3000]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+3080]
	adc r8, QWORD PTR [rdi+3008]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3016], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3024], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3032], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3040], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3048], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3056], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3064], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3072], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3080], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+3016]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3016], rdx
	mov rdx, QWORD PTR [rdi+3024]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3024], rdx
	mov rdx, QWORD PTR [rdi+3032]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3032], rdx
	mov rdx, QWORD PTR [rdi+3040]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3040], rdx
	mov rdx, QWORD PTR [rdi+3048]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3048], rdx
	mov rdx, QWORD PTR [rdi+3056]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3056], rdx
	mov rdx, QWORD PTR [rdi+3064]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3064], rdx
	mov rdx, QWORD PTR [rdi+3072]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3072], rdx
	mov rdx, QWORD PTR [rdi+3080]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3080], rdx
	mov r12, rsi
	mov esi, 3088
	mov edx, 2152
	mov ecx, 3016
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3160
	mov edx, 3088
	mov ecx, 352
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov rdx, QWORD PTR [rdi+3160]
	or rdx, QWORD PTR [rdi+3168]
	or rdx, QWORD PTR [rdi+3176]
	or rdx, QWORD PTR [rdi+3184]
	or rdx, QWORD PTR [rdi+3192]
	or rdx, QWORD PTR [rdi+3200]
	or rdx, QWORD PTR [rdi+3208]
	or rdx, QWORD PTR [rdi+3216]
	or rdx, QWORD PTR [rdi+3224]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rcx, QWORD PTR [rdi+3232]
	mov rax, QWORD PTR [rdi+2656]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+58], rax
	mov rax, QWORD PTR [rdi+2664]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+50], rax
	mov rax, QWORD PTR [rdi+2672]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+42], rax
	mov rax, QWORD PTR [rdi+2680]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+34], rax
	mov rax, QWORD PTR [rdi+2688]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+26], rax
	mov rax, QWORD PTR [rdi+2696]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+18], rax
	mov rax, QWORD PTR [rdi+2704]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+10], rax
	mov rax, QWORD PTR [rdi+2712]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+2], rax
	mov rax, QWORD PTR [rdi+2720]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi], dl
	mov rdx, rax
	mov BYTE PTR [rsi+1], dl
	mov rax, QWORD PTR [rdi+3160]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+124], rax
	mov rax, QWORD PTR [rdi+3168]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+116], rax
	mov rax, QWORD PTR [rdi+3176]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+108], rax
	mov rax, QWORD PTR [rdi+3184]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+100], rax
	mov rax, QWORD PTR [rdi+3192]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+92], rax
	mov rax, QWORD PTR [rdi+3200]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+84], rax
	mov rax, QWORD PTR [rdi+3208]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+76], rax
	mov rax, QWORD PTR [rdi+3216]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+68], rax
	mov rax, QWORD PTR [rdi+3224]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi+66], dl
	mov rdx, rax
	mov BYTE PTR [rsi+67], dl
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6
