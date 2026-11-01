// The functions of `src/p224_point.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p224_point_add:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3584], edi
	mov edi, eax
	mov eax, 3424
	mov ecx, 3328
	mov edx, 3648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3456
	mov ecx, 3360
	mov edx, 3680
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3488
	mov ecx, 3392
	mov edx, 3712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3360
	mov ecx, 3328
	mov edx, 3744
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3456
	mov ecx, 3424
	mov edx, 3776
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3776
	mov ecx, 3744
	mov edx, 3744
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3680
	mov ecx, 3648
	mov edx, 3776
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3776
	mov ecx, 3744
	mov edx, 3744
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3392
	mov ecx, 3328
	mov edx, 3776
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3488
	mov ecx, 3424
	mov edx, 3808
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3808
	mov ecx, 3776
	mov edx, 3776
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3648
	mov edx, 3808
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3808
	mov ecx, 3776
	mov edx, 3776
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3392
	mov ecx, 3360
	mov edx, 3808
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3488
	mov ecx, 3456
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3232
	mov ecx, 3808
	mov edx, 3808
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3680
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3232
	mov ecx, 3808
	mov edx, 3808
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3776
	mov ecx, 3520
	mov edx, 3296
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3552
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3296
	mov ecx, 3232
	mov edx, 3296
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3296
	mov ecx, 3680
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3296
	mov ecx, 3680
	mov edx, 3296
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3296
	mov ecx, 3232
	mov edx, 3264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3648
	mov ecx, 3648
	mov edx, 3680
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3648
	mov ecx, 3680
	mov edx, 3680
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3520
	mov edx, 3712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3776
	mov ecx, 3552
	mov edx, 3776
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3680
	mov edx, 3680
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3648
	mov edx, 3712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3520
	mov edx, 3712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3776
	mov edx, 3776
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3776
	mov ecx, 3680
	mov edx, 3648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3648
	mov ecx, 3264
	mov edx, 3264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3776
	mov ecx, 3808
	mov edx, 3648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3232
	mov ecx, 3744
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3648
	mov ecx, 3232
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3680
	mov ecx, 3744
	mov edx, 3648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3296
	mov ecx, 3808
	mov edx, 3296
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3648
	mov ecx, 3296
	mov edx, 3296
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [edi+3584]
	ret
	.p2align 6

vg_p224_point_double:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+3584], edi
	mov edi, eax
	mov eax, 3328
	mov ecx, 3328
	mov edx, 3648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3360
	mov ecx, 3360
	mov edx, 3680
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3392
	mov ecx, 3392
	mov edx, 3712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3360
	mov ecx, 3328
	mov edx, 3744
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3360
	mov ecx, 3328
	mov edx, 3776
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3776
	mov ecx, 3744
	mov edx, 3744
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3680
	mov ecx, 3648
	mov edx, 3776
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3776
	mov ecx, 3744
	mov edx, 3744
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3392
	mov ecx, 3328
	mov edx, 3776
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3392
	mov ecx, 3328
	mov edx, 3808
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3808
	mov ecx, 3776
	mov edx, 3776
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3648
	mov edx, 3808
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3808
	mov ecx, 3776
	mov edx, 3776
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3392
	mov ecx, 3360
	mov edx, 3808
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3392
	mov ecx, 3360
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3232
	mov ecx, 3808
	mov edx, 3808
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3680
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3232
	mov ecx, 3808
	mov edx, 3808
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3776
	mov ecx, 3520
	mov edx, 3296
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3552
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3296
	mov ecx, 3232
	mov edx, 3296
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3296
	mov ecx, 3680
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3296
	mov ecx, 3680
	mov edx, 3296
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3296
	mov ecx, 3232
	mov edx, 3264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3648
	mov ecx, 3648
	mov edx, 3680
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3648
	mov ecx, 3680
	mov edx, 3680
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3520
	mov edx, 3712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3776
	mov ecx, 3552
	mov edx, 3776
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3680
	mov edx, 3680
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3648
	mov edx, 3712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3520
	mov edx, 3712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3712
	mov ecx, 3776
	mov edx, 3776
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3776
	mov ecx, 3680
	mov edx, 3648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3648
	mov ecx, 3264
	mov edx, 3264
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3776
	mov ecx, 3808
	mov edx, 3648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3232
	mov ecx, 3744
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3648
	mov ecx, 3232
	mov edx, 3232
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3680
	mov ecx, 3744
	mov edx, 3648
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3296
	mov ecx, 3808
	mov edx, 3296
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3648
	mov ecx, 3296
	mov edx, 3296
	push eax
	push ecx
	push edx
	push edi
	call {vg_p224_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [edi+3584]
	ret
	.p2align 6
