// The functions of `src/internal/vg_sha512_224_init_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_224_init_core:
	mov eax, DWORD PTR [esp+4]
	mov ecx, 424955298
	mov DWORD PTR [eax], ecx
	mov ecx, -1942145080
	mov DWORD PTR [eax+4], ecx
	mov ecx, -1982016298
	mov DWORD PTR [eax+8], ecx
	mov ecx, 1944164710
	mov DWORD PTR [eax+12], ecx
	mov ecx, 855612546
	mov DWORD PTR [eax+16], ecx
	mov ecx, 502970286
	mov DWORD PTR [eax+20], ecx
	mov ecx, 1479516111
	mov DWORD PTR [eax+24], ecx
	mov ecx, 1738396948
	mov DWORD PTR [eax+28], ecx
	mov ecx, 2077511080
	mov DWORD PTR [eax+32], ecx
	mov ecx, 258812777
	mov DWORD PTR [eax+36], ecx
	mov ecx, 79989058
	mov DWORD PTR [eax+40], ecx
	mov ecx, 2011393907
	mov DWORD PTR [eax+44], ecx
	mov ecx, 1780299464
	mov DWORD PTR [eax+48], ecx
	mov ecx, 1067287976
	mov DWORD PTR [eax+52], ecx
	mov ecx, -1848208735
	mov DWORD PTR [eax+56], ecx
	mov ecx, 286451373
	mov DWORD PTR [eax+60], ecx
	ret
	.p2align 6
