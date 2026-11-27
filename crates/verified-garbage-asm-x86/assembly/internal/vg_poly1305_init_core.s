// The functions of `src/internal/vg_poly1305_init_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_init_core:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [ecx]
	mov DWORD PTR [eax+24], edx
	mov edx, DWORD PTR [ecx+4]
	mov DWORD PTR [eax+28], edx
	mov edx, DWORD PTR [ecx+8]
	mov DWORD PTR [eax+32], edx
	mov edx, DWORD PTR [ecx+12]
	mov DWORD PTR [eax+36], edx
	mov edx, DWORD PTR [ecx+16]
	mov DWORD PTR [eax+40], edx
	mov edx, DWORD PTR [ecx+20]
	mov DWORD PTR [eax+44], edx
	mov edx, DWORD PTR [ecx+24]
	mov DWORD PTR [eax+48], edx
	mov edx, DWORD PTR [ecx+28]
	mov DWORD PTR [eax+52], edx
	mov edx, 0
	mov DWORD PTR [eax], edx
	mov DWORD PTR [eax+4], edx
	mov DWORD PTR [eax+8], edx
	mov DWORD PTR [eax+12], edx
	mov DWORD PTR [eax+16], edx
	mov DWORD PTR [eax+20], edx
	ret
	.p2align 6
