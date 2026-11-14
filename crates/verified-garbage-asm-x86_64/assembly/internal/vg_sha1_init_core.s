// The functions of `src/internal/vg_sha1_init_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_init_core:
	mov eax, 1732584193
	mov DWORD PTR [rdi], eax
	mov eax, -271733879
	mov DWORD PTR [rdi+4], eax
	mov eax, -1732584194
	mov DWORD PTR [rdi+8], eax
	mov eax, 271733878
	mov DWORD PTR [rdi+12], eax
	mov eax, -1009589776
	mov DWORD PTR [rdi+16], eax
	ret
	.p2align 6
