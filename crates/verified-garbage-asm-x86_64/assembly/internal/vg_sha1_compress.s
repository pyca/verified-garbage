// The functions of `src/internal/vg_sha1_compress.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_compress:
	mov QWORD PTR [rcx+64], rbx
	mov QWORD PTR [rcx+72], rbp
	mov QWORD PTR [rcx+80], r12
	mov QWORD PTR [rcx+88], r13
	mov QWORD PTR [rcx+96], r14
	mov QWORD PTR [rcx+104], r15
	test rdx, rdx
	je 20f
22:
	mov eax, DWORD PTR [rdi]
	mov ebx, DWORD PTR [rdi+4]
	mov ebp, DWORD PTR [rdi+8]
	mov r8d, DWORD PTR [rdi+12]
	mov r9d, DWORD PTR [rdi+16]
	mov r13d, DWORD PTR [rsi]
	bswap r13d
	mov DWORD PTR [rcx], r13d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, ebx
	xor r14d, r8d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, 1518500249
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rsi+4]
	bswap r13d
	mov DWORD PTR [rcx+4], r13d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, eax
	xor r14d, ebp
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, 1518500249
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rsi+8]
	bswap r13d
	mov DWORD PTR [rcx+8], r13d
	mov r14d, eax
	xor r14d, ebx
	and r14d, r9d
	xor r14d, ebx
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, 1518500249
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rsi+12]
	bswap r13d
	mov DWORD PTR [rcx+12], r13d
	mov r14d, r9d
	xor r14d, eax
	and r14d, r8d
	xor r14d, eax
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, 1518500249
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rsi+16]
	bswap r13d
	mov DWORD PTR [rcx+16], r13d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, ebp
	xor r14d, r9d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, 1518500249
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rsi+20]
	bswap r13d
	mov DWORD PTR [rcx+20], r13d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, ebx
	xor r14d, r8d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, 1518500249
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rsi+24]
	bswap r13d
	mov DWORD PTR [rcx+24], r13d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, eax
	xor r14d, ebp
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, 1518500249
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rsi+28]
	bswap r13d
	mov DWORD PTR [rcx+28], r13d
	mov r14d, eax
	xor r14d, ebx
	and r14d, r9d
	xor r14d, ebx
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, 1518500249
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rsi+32]
	bswap r13d
	mov DWORD PTR [rcx+32], r13d
	mov r14d, r9d
	xor r14d, eax
	and r14d, r8d
	xor r14d, eax
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, 1518500249
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rsi+36]
	bswap r13d
	mov DWORD PTR [rcx+36], r13d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, ebp
	xor r14d, r9d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, 1518500249
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rsi+40]
	bswap r13d
	mov DWORD PTR [rcx+40], r13d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, ebx
	xor r14d, r8d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, 1518500249
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rsi+44]
	bswap r13d
	mov DWORD PTR [rcx+44], r13d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, eax
	xor r14d, ebp
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, 1518500249
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rsi+48]
	bswap r13d
	mov DWORD PTR [rcx+48], r13d
	mov r14d, eax
	xor r14d, ebx
	and r14d, r9d
	xor r14d, ebx
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, 1518500249
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rsi+52]
	bswap r13d
	mov DWORD PTR [rcx+52], r13d
	mov r14d, r9d
	xor r14d, eax
	and r14d, r8d
	xor r14d, eax
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, 1518500249
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rsi+56]
	bswap r13d
	mov DWORD PTR [rcx+56], r13d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, ebp
	xor r14d, r9d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, 1518500249
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rsi+60]
	bswap r13d
	mov DWORD PTR [rcx+60], r13d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, ebx
	xor r14d, r8d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, 1518500249
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx]
	ror r13d, 31
	mov DWORD PTR [rcx], r13d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, eax
	xor r14d, ebp
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, 1518500249
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+4]
	ror r13d, 31
	mov DWORD PTR [rcx+4], r13d
	mov r14d, eax
	xor r14d, ebx
	and r14d, r9d
	xor r14d, ebx
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, 1518500249
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+8]
	ror r13d, 31
	mov DWORD PTR [rcx+8], r13d
	mov r14d, r9d
	xor r14d, eax
	and r14d, r8d
	xor r14d, eax
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, 1518500249
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+12]
	ror r13d, 31
	mov DWORD PTR [rcx+12], r13d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, ebp
	xor r14d, r9d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, 1518500249
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+16]
	ror r13d, 31
	mov DWORD PTR [rcx+16], r13d
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, 1859775393
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+20]
	ror r13d, 31
	mov DWORD PTR [rcx+20], r13d
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, 1859775393
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+24]
	ror r13d, 31
	mov DWORD PTR [rcx+24], r13d
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, 1859775393
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+28]
	ror r13d, 31
	mov DWORD PTR [rcx+28], r13d
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, 1859775393
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+32]
	ror r13d, 31
	mov DWORD PTR [rcx+32], r13d
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, 1859775393
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+36]
	ror r13d, 31
	mov DWORD PTR [rcx+36], r13d
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, 1859775393
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+40]
	ror r13d, 31
	mov DWORD PTR [rcx+40], r13d
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, 1859775393
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+44]
	ror r13d, 31
	mov DWORD PTR [rcx+44], r13d
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, 1859775393
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+48]
	ror r13d, 31
	mov DWORD PTR [rcx+48], r13d
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, 1859775393
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+52]
	ror r13d, 31
	mov DWORD PTR [rcx+52], r13d
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, 1859775393
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+56]
	ror r13d, 31
	mov DWORD PTR [rcx+56], r13d
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, 1859775393
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+60]
	ror r13d, 31
	mov DWORD PTR [rcx+60], r13d
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, 1859775393
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx]
	ror r13d, 31
	mov DWORD PTR [rcx], r13d
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, 1859775393
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+4]
	ror r13d, 31
	mov DWORD PTR [rcx+4], r13d
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, 1859775393
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+8]
	ror r13d, 31
	mov DWORD PTR [rcx+8], r13d
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, 1859775393
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+12]
	ror r13d, 31
	mov DWORD PTR [rcx+12], r13d
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, 1859775393
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+16]
	ror r13d, 31
	mov DWORD PTR [rcx+16], r13d
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, 1859775393
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+20]
	ror r13d, 31
	mov DWORD PTR [rcx+20], r13d
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, 1859775393
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+24]
	ror r13d, 31
	mov DWORD PTR [rcx+24], r13d
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, 1859775393
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+28]
	ror r13d, 31
	mov DWORD PTR [rcx+28], r13d
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, 1859775393
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+32]
	ror r13d, 31
	mov DWORD PTR [rcx+32], r13d
	mov r14d, ebx
	or r14d, ebp
	and r14d, r8d
	mov r15d, ebx
	and r15d, ebp
	or r14d, r15d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, -1894007588
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+36]
	ror r13d, 31
	mov DWORD PTR [rcx+36], r13d
	mov r14d, eax
	or r14d, ebx
	and r14d, ebp
	mov r15d, eax
	and r15d, ebx
	or r14d, r15d
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, -1894007588
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+40]
	ror r13d, 31
	mov DWORD PTR [rcx+40], r13d
	mov r14d, r9d
	or r14d, eax
	and r14d, ebx
	mov r15d, r9d
	and r15d, eax
	or r14d, r15d
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, -1894007588
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+44]
	ror r13d, 31
	mov DWORD PTR [rcx+44], r13d
	mov r14d, r8d
	or r14d, r9d
	and r14d, eax
	mov r15d, r8d
	and r15d, r9d
	or r14d, r15d
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, -1894007588
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+48]
	ror r13d, 31
	mov DWORD PTR [rcx+48], r13d
	mov r14d, ebp
	or r14d, r8d
	and r14d, r9d
	mov r15d, ebp
	and r15d, r8d
	or r14d, r15d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, -1894007588
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+52]
	ror r13d, 31
	mov DWORD PTR [rcx+52], r13d
	mov r14d, ebx
	or r14d, ebp
	and r14d, r8d
	mov r15d, ebx
	and r15d, ebp
	or r14d, r15d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, -1894007588
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+56]
	ror r13d, 31
	mov DWORD PTR [rcx+56], r13d
	mov r14d, eax
	or r14d, ebx
	and r14d, ebp
	mov r15d, eax
	and r15d, ebx
	or r14d, r15d
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, -1894007588
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+60]
	ror r13d, 31
	mov DWORD PTR [rcx+60], r13d
	mov r14d, r9d
	or r14d, eax
	and r14d, ebx
	mov r15d, r9d
	and r15d, eax
	or r14d, r15d
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, -1894007588
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx]
	ror r13d, 31
	mov DWORD PTR [rcx], r13d
	mov r14d, r8d
	or r14d, r9d
	and r14d, eax
	mov r15d, r8d
	and r15d, r9d
	or r14d, r15d
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, -1894007588
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+4]
	ror r13d, 31
	mov DWORD PTR [rcx+4], r13d
	mov r14d, ebp
	or r14d, r8d
	and r14d, r9d
	mov r15d, ebp
	and r15d, r8d
	or r14d, r15d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, -1894007588
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+8]
	ror r13d, 31
	mov DWORD PTR [rcx+8], r13d
	mov r14d, ebx
	or r14d, ebp
	and r14d, r8d
	mov r15d, ebx
	and r15d, ebp
	or r14d, r15d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, -1894007588
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+12]
	ror r13d, 31
	mov DWORD PTR [rcx+12], r13d
	mov r14d, eax
	or r14d, ebx
	and r14d, ebp
	mov r15d, eax
	and r15d, ebx
	or r14d, r15d
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, -1894007588
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+16]
	ror r13d, 31
	mov DWORD PTR [rcx+16], r13d
	mov r14d, r9d
	or r14d, eax
	and r14d, ebx
	mov r15d, r9d
	and r15d, eax
	or r14d, r15d
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, -1894007588
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+20]
	ror r13d, 31
	mov DWORD PTR [rcx+20], r13d
	mov r14d, r8d
	or r14d, r9d
	and r14d, eax
	mov r15d, r8d
	and r15d, r9d
	or r14d, r15d
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, -1894007588
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+24]
	ror r13d, 31
	mov DWORD PTR [rcx+24], r13d
	mov r14d, ebp
	or r14d, r8d
	and r14d, r9d
	mov r15d, ebp
	and r15d, r8d
	or r14d, r15d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, -1894007588
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+28]
	ror r13d, 31
	mov DWORD PTR [rcx+28], r13d
	mov r14d, ebx
	or r14d, ebp
	and r14d, r8d
	mov r15d, ebx
	and r15d, ebp
	or r14d, r15d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, -1894007588
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+32]
	ror r13d, 31
	mov DWORD PTR [rcx+32], r13d
	mov r14d, eax
	or r14d, ebx
	and r14d, ebp
	mov r15d, eax
	and r15d, ebx
	or r14d, r15d
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, -1894007588
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+36]
	ror r13d, 31
	mov DWORD PTR [rcx+36], r13d
	mov r14d, r9d
	or r14d, eax
	and r14d, ebx
	mov r15d, r9d
	and r15d, eax
	or r14d, r15d
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, -1894007588
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+40]
	ror r13d, 31
	mov DWORD PTR [rcx+40], r13d
	mov r14d, r8d
	or r14d, r9d
	and r14d, eax
	mov r15d, r8d
	and r15d, r9d
	or r14d, r15d
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, -1894007588
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+44]
	ror r13d, 31
	mov DWORD PTR [rcx+44], r13d
	mov r14d, ebp
	or r14d, r8d
	and r14d, r9d
	mov r15d, ebp
	and r15d, r8d
	or r14d, r15d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, -1894007588
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+48]
	ror r13d, 31
	mov DWORD PTR [rcx+48], r13d
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, -899497514
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+52]
	ror r13d, 31
	mov DWORD PTR [rcx+52], r13d
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, -899497514
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+56]
	ror r13d, 31
	mov DWORD PTR [rcx+56], r13d
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, -899497514
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+60]
	ror r13d, 31
	mov DWORD PTR [rcx+60], r13d
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, -899497514
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx]
	ror r13d, 31
	mov DWORD PTR [rcx], r13d
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, -899497514
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+4]
	ror r13d, 31
	mov DWORD PTR [rcx+4], r13d
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, -899497514
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+8]
	ror r13d, 31
	mov DWORD PTR [rcx+8], r13d
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, -899497514
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+12]
	ror r13d, 31
	mov DWORD PTR [rcx+12], r13d
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, -899497514
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+16]
	ror r13d, 31
	mov DWORD PTR [rcx+16], r13d
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, -899497514
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+20]
	ror r13d, 31
	mov DWORD PTR [rcx+20], r13d
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, -899497514
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+24]
	ror r13d, 31
	mov DWORD PTR [rcx+24], r13d
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, -899497514
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+28]
	ror r13d, 31
	mov DWORD PTR [rcx+28], r13d
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, -899497514
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+32]
	ror r13d, 31
	mov DWORD PTR [rcx+32], r13d
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, -899497514
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+36]
	ror r13d, 31
	mov DWORD PTR [rcx+36], r13d
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, -899497514
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+8]
	xor r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+40]
	ror r13d, 31
	mov DWORD PTR [rcx+40], r13d
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, -899497514
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	mov r13d, DWORD PTR [rcx+32]
	xor r13d, DWORD PTR [rcx+12]
	xor r13d, DWORD PTR [rcx+52]
	xor r13d, DWORD PTR [rcx+44]
	ror r13d, 31
	mov DWORD PTR [rcx+44], r13d
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	mov r15d, eax
	ror r15d, 27
	add r15d, r14d
	add r15d, r9d
	add r15d, -899497514
	add r15d, r13d
	mov r9d, r15d
	ror ebx, 2
	mov r13d, DWORD PTR [rcx+36]
	xor r13d, DWORD PTR [rcx+16]
	xor r13d, DWORD PTR [rcx+56]
	xor r13d, DWORD PTR [rcx+48]
	ror r13d, 31
	mov DWORD PTR [rcx+48], r13d
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	mov r15d, r9d
	ror r15d, 27
	add r15d, r14d
	add r15d, r8d
	add r15d, -899497514
	add r15d, r13d
	mov r8d, r15d
	ror eax, 2
	mov r13d, DWORD PTR [rcx+40]
	xor r13d, DWORD PTR [rcx+20]
	xor r13d, DWORD PTR [rcx+60]
	xor r13d, DWORD PTR [rcx+52]
	ror r13d, 31
	mov DWORD PTR [rcx+52], r13d
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	mov r15d, r8d
	ror r15d, 27
	add r15d, r14d
	add r15d, ebp
	add r15d, -899497514
	add r15d, r13d
	mov ebp, r15d
	ror r9d, 2
	mov r13d, DWORD PTR [rcx+44]
	xor r13d, DWORD PTR [rcx+24]
	xor r13d, DWORD PTR [rcx]
	xor r13d, DWORD PTR [rcx+56]
	ror r13d, 31
	mov DWORD PTR [rcx+56], r13d
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	mov r15d, ebp
	ror r15d, 27
	add r15d, r14d
	add r15d, ebx
	add r15d, -899497514
	add r15d, r13d
	mov ebx, r15d
	ror r8d, 2
	mov r13d, DWORD PTR [rcx+48]
	xor r13d, DWORD PTR [rcx+28]
	xor r13d, DWORD PTR [rcx+4]
	xor r13d, DWORD PTR [rcx+60]
	ror r13d, 31
	mov DWORD PTR [rcx+60], r13d
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	mov r15d, ebx
	ror r15d, 27
	add r15d, r14d
	add r15d, eax
	add r15d, -899497514
	add r15d, r13d
	mov eax, r15d
	ror ebp, 2
	add eax, DWORD PTR [rdi]
	add ebx, DWORD PTR [rdi+4]
	add ebp, DWORD PTR [rdi+8]
	add r8d, DWORD PTR [rdi+12]
	add r9d, DWORD PTR [rdi+16]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+4], ebx
	mov DWORD PTR [rdi+8], ebp
	mov DWORD PTR [rdi+12], r8d
	mov DWORD PTR [rdi+16], r9d
	add rsi, 64
	sub rdx, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [rcx+64]
	mov rbp, QWORD PTR [rcx+72]
	mov r12, QWORD PTR [rcx+80]
	mov r13, QWORD PTR [rcx+88]
	mov r14, QWORD PTR [rcx+96]
	mov r15, QWORD PTR [rcx+104]
	ret
	.p2align 6
