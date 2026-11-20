// The functions of `src/internal/vg_sha224_init_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha224_init_core:
	mov eax, DWORD PTR [esp+4]
	mov ecx, -1056596264
	mov DWORD PTR [eax], ecx
	mov ecx, 914150663
	mov DWORD PTR [eax+4], ecx
	mov ecx, 812702999
	mov DWORD PTR [eax+8], ecx
	mov ecx, -150054599
	mov DWORD PTR [eax+12], ecx
	mov ecx, -4191439
	mov DWORD PTR [eax+16], ecx
	mov ecx, 1750603025
	mov DWORD PTR [eax+20], ecx
	mov ecx, 1694076839
	mov DWORD PTR [eax+24], ecx
	mov ecx, -1090891868
	mov DWORD PTR [eax+28], ecx
	ret
	.p2align 6
