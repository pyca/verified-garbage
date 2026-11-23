// The functions of `src/internal/vg_ecdsa_p256_verify_peer_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_verify_peer_adx:
	movabs rax, 3
	mov QWORD PTR [rdi+1312], rax
	movabs rax, -17179869185
	mov QWORD PTR [rdi+1320], rax
	movabs rax, -2
	mov QWORD PTR [rdi+1328], rax
	movabs rax, 21474836477
	mov QWORD PTR [rdi+1336], rax
	movabs rax, -2838148052449706529
	mov QWORD PTR [rdi+1344], rax
	movabs rax, -5985277524727025520
	mov QWORD PTR [rdi+1352], rax
	movabs rax, -1899920169839284522
	mov QWORD PTR [rdi+1360], rax
	movabs rax, -2580555864783501260
	mov QWORD PTR [rdi+1368], rax
	mov rdx, r9
	add rdx, 33
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1240], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	ret
	.p2align 6
