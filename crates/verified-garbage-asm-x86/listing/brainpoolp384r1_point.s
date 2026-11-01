// The functions of `src/brainpoolp384r1_point.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp384r1_point_add:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3360], edi
	mov edi, eax
	mov eax, 3120
	mov ecx, 2976
	mov edx, 3424
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3168
	mov ecx, 3024
	mov edx, 3472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3216
	mov ecx, 3072
	mov edx, 3520
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3024
	mov ecx, 2976
	mov edx, 3568
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3168
	mov ecx, 3120
	mov edx, 3616
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3616
	mov ecx, 3568
	mov edx, 3568
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3472
	mov ecx, 3424
	mov edx, 3616
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3616
	mov ecx, 3568
	mov edx, 3568
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3072
	mov ecx, 2976
	mov edx, 3616
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3216
	mov ecx, 3120
	mov edx, 3664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3664
	mov ecx, 3616
	mov edx, 3616
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3424
	mov edx, 3664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3664
	mov ecx, 3616
	mov edx, 3616
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3072
	mov ecx, 3024
	mov edx, 3664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3216
	mov ecx, 3168
	mov edx, 2832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2832
	mov ecx, 3664
	mov edx, 3664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3472
	mov edx, 2832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2832
	mov ecx, 3664
	mov edx, 3664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3616
	mov ecx, 3264
	mov edx, 2928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3312
	mov edx, 2832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2928
	mov ecx, 2832
	mov edx, 2928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2928
	mov ecx, 3472
	mov edx, 2832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2928
	mov ecx, 3472
	mov edx, 2928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2928
	mov ecx, 2832
	mov edx, 2880
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3424
	mov ecx, 3424
	mov edx, 3472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3424
	mov ecx, 3472
	mov edx, 3472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3264
	mov edx, 3520
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3616
	mov ecx, 3312
	mov edx, 3616
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3472
	mov edx, 3472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3424
	mov edx, 3520
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3264
	mov edx, 3520
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3616
	mov edx, 3616
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3616
	mov ecx, 3472
	mov edx, 3424
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3424
	mov ecx, 2880
	mov edx, 2880
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3616
	mov ecx, 3664
	mov edx, 3424
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2832
	mov ecx, 3568
	mov edx, 2832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3424
	mov ecx, 2832
	mov edx, 2832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3472
	mov ecx, 3568
	mov edx, 3424
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2928
	mov ecx, 3664
	mov edx, 2928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3424
	mov ecx, 2928
	mov edx, 2928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [edi+3360]
	ret
	.p2align 6

vg_brainpoolp384r1_point_double:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3360], edi
	mov edi, eax
	mov eax, 2976
	mov ecx, 2976
	mov edx, 3424
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3024
	mov ecx, 3024
	mov edx, 3472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3072
	mov ecx, 3072
	mov edx, 3520
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3024
	mov ecx, 2976
	mov edx, 3568
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3024
	mov ecx, 2976
	mov edx, 3616
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3616
	mov ecx, 3568
	mov edx, 3568
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3472
	mov ecx, 3424
	mov edx, 3616
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3616
	mov ecx, 3568
	mov edx, 3568
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3072
	mov ecx, 2976
	mov edx, 3616
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3072
	mov ecx, 2976
	mov edx, 3664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3664
	mov ecx, 3616
	mov edx, 3616
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3424
	mov edx, 3664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3664
	mov ecx, 3616
	mov edx, 3616
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3072
	mov ecx, 3024
	mov edx, 3664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3072
	mov ecx, 3024
	mov edx, 2832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2832
	mov ecx, 3664
	mov edx, 3664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3472
	mov edx, 2832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2832
	mov ecx, 3664
	mov edx, 3664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3616
	mov ecx, 3264
	mov edx, 2928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3312
	mov edx, 2832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2928
	mov ecx, 2832
	mov edx, 2928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2928
	mov ecx, 3472
	mov edx, 2832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2928
	mov ecx, 3472
	mov edx, 2928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2928
	mov ecx, 2832
	mov edx, 2880
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3424
	mov ecx, 3424
	mov edx, 3472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3424
	mov ecx, 3472
	mov edx, 3472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3264
	mov edx, 3520
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3616
	mov ecx, 3312
	mov edx, 3616
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3472
	mov edx, 3472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3424
	mov edx, 3520
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3264
	mov edx, 3520
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3520
	mov ecx, 3616
	mov edx, 3616
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3616
	mov ecx, 3472
	mov edx, 3424
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3424
	mov ecx, 2880
	mov edx, 2880
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3616
	mov ecx, 3664
	mov edx, 3424
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2832
	mov ecx, 3568
	mov edx, 2832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3424
	mov ecx, 2832
	mov edx, 2832
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3472
	mov ecx, 3568
	mov edx, 3424
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2928
	mov ecx, 3664
	mov edx, 2928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3424
	mov ecx, 2928
	mov edx, 2928
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [edi+3360]
	ret
	.p2align 6
