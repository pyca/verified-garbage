// The functions of `src/internal/vg_sha1_init_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_init_core:
	mov eax, DWORD PTR [esp+4]
	mov ecx, 1732584193
	mov DWORD PTR [eax], ecx
	mov ecx, -271733879
	mov DWORD PTR [eax+4], ecx
	mov ecx, -1732584194
	mov DWORD PTR [eax+8], ecx
	mov ecx, 271733878
	mov DWORD PTR [eax+12], ecx
	mov ecx, -1009589776
	mov DWORD PTR [eax+16], ecx
	ret
	.p2align 6
