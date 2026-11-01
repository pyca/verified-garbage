// The functions of `src/internal/vg_brainpoolp512r1_check_point.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_check_point:
	movq xmm0, rbx
	movq xmm1, rbp
	movq xmm2, r12
	movq xmm3, r13
	movq xmm4, r14
	movq xmm5, r15
	mov rdx, QWORD PTR [rdi+2176]
	sub rdx, QWORD PTR [rdi+64]
	mov rdx, QWORD PTR [rdi+2184]
	sbb rdx, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+2192]
	sbb rdx, QWORD PTR [rdi+80]
	mov rdx, QWORD PTR [rdi+2200]
	sbb rdx, QWORD PTR [rdi+88]
	mov rdx, QWORD PTR [rdi+2208]
	sbb rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+2216]
	sbb rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+2224]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+2232]
	sbb rdx, QWORD PTR [rdi+120]
	sbb rax, rax
	mov rdx, rax
	mov rax, QWORD PTR [rdi+2880]
	and rax, rdx
	mov QWORD PTR [rdi+2880], rax
	mov rdx, QWORD PTR [rdi+2368]
	sub rdx, QWORD PTR [rdi+64]
	mov rdx, QWORD PTR [rdi+2376]
	sbb rdx, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+2384]
	sbb rdx, QWORD PTR [rdi+80]
	mov rdx, QWORD PTR [rdi+2392]
	sbb rdx, QWORD PTR [rdi+88]
	mov rdx, QWORD PTR [rdi+2400]
	sbb rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+2408]
	sbb rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+2416]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+2424]
	sbb rdx, QWORD PTR [rdi+120]
	sbb rax, rax
	mov rdx, rax
	mov rax, QWORD PTR [rdi+2880]
	and rax, rdx
	mov QWORD PTR [rdi+2880], rax
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2240], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2248], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2256], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2264], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2272], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2280], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2288], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2296], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2240]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2240], rdx
	mov rdx, QWORD PTR [rdi+2248]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2248], rdx
	mov rdx, QWORD PTR [rdi+2256]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2256], rdx
	mov rdx, QWORD PTR [rdi+2264]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2264], rdx
	mov rdx, QWORD PTR [rdi+2272]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2272], rdx
	mov rdx, QWORD PTR [rdi+2280]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2280], rdx
	mov rdx, QWORD PTR [rdi+2288]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2288], rdx
	mov rdx, QWORD PTR [rdi+2296]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2296], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2368]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2368]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2376]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2368]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2376]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2384]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2368]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2376]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2384]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2392]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2368]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2376]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2384]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2392]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2400]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2368]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2376]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2384]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2392]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2400]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2408]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2368]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2376]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2384]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2392]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2400]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2408]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2416]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2368]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2376]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2384]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2392]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2400]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2408]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2416]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2424]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2376]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2384]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2392]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2400]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2408]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2416]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2424]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2384]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2392]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2400]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2408]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2416]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2424]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2392]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2400]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2408]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2416]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2584]
	mov rax, QWORD PTR [rdi+2424]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2400]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2408]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2416]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2592]
	mov rax, QWORD PTR [rdi+2424]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2408]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2416]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2600]
	mov rax, QWORD PTR [rdi+2424]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2416]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2608]
	mov rax, QWORD PTR [rdi+2424]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2616]
	mov rax, QWORD PTR [rdi+2424]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2304], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2312], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2320], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2328], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2336], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2344], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2352], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2360], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2304]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2304], rdx
	mov rdx, QWORD PTR [rdi+2312]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2312], rdx
	mov rdx, QWORD PTR [rdi+2320]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2320], rdx
	mov rdx, QWORD PTR [rdi+2328]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2328], rdx
	mov rdx, QWORD PTR [rdi+2336]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2336], rdx
	mov rdx, QWORD PTR [rdi+2344]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2344], rdx
	mov rdx, QWORD PTR [rdi+2352]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2352], rdx
	mov rdx, QWORD PTR [rdi+2360]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2360], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2304]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2312]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2304]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2320]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2312]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2304]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2328]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2320]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2312]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2304]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2336]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2328]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2320]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2312]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2304]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2344]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2336]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2328]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2320]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2312]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2304]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2352]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2344]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2336]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2328]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2320]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2312]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2304]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2360]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2352]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2344]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2336]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2328]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2320]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2312]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2304]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2360]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2352]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2344]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2336]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2328]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2320]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2312]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2360]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2352]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2344]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2336]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2328]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2320]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2360]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2352]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2344]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2336]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2328]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2360]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2352]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2344]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2336]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2360]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2352]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2344]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2360]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2352]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2360]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2432], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2440], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2448], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2456], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2464], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2472], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2480], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2488], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2432]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2432], rdx
	mov rdx, QWORD PTR [rdi+2440]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2440], rdx
	mov rdx, QWORD PTR [rdi+2448]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2448], rdx
	mov rdx, QWORD PTR [rdi+2456]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2456], rdx
	mov rdx, QWORD PTR [rdi+2464]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2464], rdx
	mov rdx, QWORD PTR [rdi+2472]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2472], rdx
	mov rdx, QWORD PTR [rdi+2480]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2480], rdx
	mov rdx, QWORD PTR [rdi+2488]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2488], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2288]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2688], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2696], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2704], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2712], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2720], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2728], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2736], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2744], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2688]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2688], rdx
	mov rdx, QWORD PTR [rdi+2696]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2696], rdx
	mov rdx, QWORD PTR [rdi+2704]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2704], rdx
	mov rdx, QWORD PTR [rdi+2712]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2712], rdx
	mov rdx, QWORD PTR [rdi+2720]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2720], rdx
	mov rdx, QWORD PTR [rdi+2728]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2728], rdx
	mov rdx, QWORD PTR [rdi+2736]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2736], rdx
	mov rdx, QWORD PTR [rdi+2744]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2744], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2688]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2688]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2696]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2688]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2696]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2704]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2688]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2696]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2704]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2712]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2688]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2696]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2704]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2712]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2720]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2688]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2696]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2704]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2712]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2720]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2688]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2696]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2704]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2712]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2720]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2688]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2696]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2704]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2712]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2720]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+2744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2696]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2704]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2712]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2720]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+2744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2704]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2712]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2720]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+2744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2712]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2720]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2728]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+2744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2720]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2728]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2736]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+2744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2728]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2736]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+2744]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2736]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+2744]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+2744]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2752], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2760], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2768], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2776], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2784], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2792], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2800], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2808], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2752]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2752], rdx
	mov rdx, QWORD PTR [rdi+2760]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2760], rdx
	mov rdx, QWORD PTR [rdi+2768]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2768], rdx
	mov rdx, QWORD PTR [rdi+2776]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2776], rdx
	mov rdx, QWORD PTR [rdi+2784]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2784], rdx
	mov rdx, QWORD PTR [rdi+2792]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2792], rdx
	mov rdx, QWORD PTR [rdi+2800]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2800], rdx
	mov rdx, QWORD PTR [rdi+2808]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2808], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+192], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+200], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+208], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+216], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+224], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rax, r10
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+232], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rax, r11
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+240], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+448]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2240]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rax, r9
	movabs rcx, -8963515518224306235
	mul rcx
	mov rcx, rax
	mov QWORD PTR [rdi+248], rcx
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+456]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2248]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+72]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+192], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+464]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2256]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+80]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+200], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+472]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2264]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+208], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+480]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2272]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+96]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+216], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+488]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2280]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+104]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+224], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+496]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2288]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+112]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+232], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2296]
	mov rax, QWORD PTR [rdi+504]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+120]
	mov rax, QWORD PTR [rdi+248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+240], r10
	mov r10d, 0
	mov QWORD PTR [rdi+248], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2688], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2696], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2704], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2712], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2720], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2728], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2736], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2744], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2688]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2688], rdx
	mov rdx, QWORD PTR [rdi+2696]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2696], rdx
	mov rdx, QWORD PTR [rdi+2704]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2704], rdx
	mov rdx, QWORD PTR [rdi+2712]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2712], rdx
	mov rdx, QWORD PTR [rdi+2720]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2720], rdx
	mov rdx, QWORD PTR [rdi+2728]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2728], rdx
	mov rdx, QWORD PTR [rdi+2736]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2736], rdx
	mov rdx, QWORD PTR [rdi+2744]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2744], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+2752]
	add r8, QWORD PTR [rdi+2688]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+2760]
	adc r8, QWORD PTR [rdi+2696]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+2768]
	adc r8, QWORD PTR [rdi+2704]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+2776]
	adc r8, QWORD PTR [rdi+2712]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+2784]
	adc r8, QWORD PTR [rdi+2720]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+2792]
	adc r8, QWORD PTR [rdi+2728]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+2800]
	adc r8, QWORD PTR [rdi+2736]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+2808]
	adc r8, QWORD PTR [rdi+2744]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2496], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2504], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2512], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2520], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2528], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2536], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2544], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2552], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2496]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2496], rdx
	mov rdx, QWORD PTR [rdi+2504]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2504], rdx
	mov rdx, QWORD PTR [rdi+2512]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2512], rdx
	mov rdx, QWORD PTR [rdi+2520]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2520], rdx
	mov rdx, QWORD PTR [rdi+2528]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2528], rdx
	mov rdx, QWORD PTR [rdi+2536]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2536], rdx
	mov rdx, QWORD PTR [rdi+2544]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2544], rdx
	mov rdx, QWORD PTR [rdi+2552]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2552], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+2496]
	add r8, QWORD PTR [rdi+2624]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+2504]
	adc r8, QWORD PTR [rdi+2632]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+2512]
	adc r8, QWORD PTR [rdi+2640]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+2520]
	adc r8, QWORD PTR [rdi+2648]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+2528]
	adc r8, QWORD PTR [rdi+2656]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+2536]
	adc r8, QWORD PTR [rdi+2664]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+2544]
	adc r8, QWORD PTR [rdi+2672]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+2552]
	adc r8, QWORD PTR [rdi+2680]
	mov QWORD PTR [rdi+248], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+192]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2752], r8
	mov r8, QWORD PTR [rdi+200]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2760], r8
	mov r8, QWORD PTR [rdi+208]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2768], r8
	mov r8, QWORD PTR [rdi+216]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2776], r8
	mov r8, QWORD PTR [rdi+224]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2784], r8
	mov r8, QWORD PTR [rdi+232]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2792], r8
	mov r8, QWORD PTR [rdi+240]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2800], r8
	mov r8, QWORD PTR [rdi+248]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2808], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2752]
	mov r8, QWORD PTR [rdi+192]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2752], rdx
	mov rdx, QWORD PTR [rdi+2760]
	mov r8, QWORD PTR [rdi+200]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2760], rdx
	mov rdx, QWORD PTR [rdi+2768]
	mov r8, QWORD PTR [rdi+208]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2768], rdx
	mov rdx, QWORD PTR [rdi+2776]
	mov r8, QWORD PTR [rdi+216]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2776], rdx
	mov rdx, QWORD PTR [rdi+2784]
	mov r8, QWORD PTR [rdi+224]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2784], rdx
	mov rdx, QWORD PTR [rdi+2792]
	mov r8, QWORD PTR [rdi+232]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2792], rdx
	mov rdx, QWORD PTR [rdi+2800]
	mov r8, QWORD PTR [rdi+240]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2800], rdx
	mov rdx, QWORD PTR [rdi+2808]
	mov r8, QWORD PTR [rdi+248]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2808], rdx
	mov r8, QWORD PTR [rdi+2432]
	sub r8, QWORD PTR [rdi+2752]
	mov QWORD PTR [rdi+192], r8
	mov r8, QWORD PTR [rdi+2440]
	sbb r8, QWORD PTR [rdi+2760]
	mov QWORD PTR [rdi+200], r8
	mov r8, QWORD PTR [rdi+2448]
	sbb r8, QWORD PTR [rdi+2768]
	mov QWORD PTR [rdi+208], r8
	mov r8, QWORD PTR [rdi+2456]
	sbb r8, QWORD PTR [rdi+2776]
	mov QWORD PTR [rdi+216], r8
	mov r8, QWORD PTR [rdi+2464]
	sbb r8, QWORD PTR [rdi+2784]
	mov QWORD PTR [rdi+224], r8
	mov r8, QWORD PTR [rdi+2472]
	sbb r8, QWORD PTR [rdi+2792]
	mov QWORD PTR [rdi+232], r8
	mov r8, QWORD PTR [rdi+2480]
	sbb r8, QWORD PTR [rdi+2800]
	mov QWORD PTR [rdi+240], r8
	mov r8, QWORD PTR [rdi+2488]
	sbb r8, QWORD PTR [rdi+2808]
	mov QWORD PTR [rdi+248], r8
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+2688], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+2696], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+2704], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+2712], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+2720], rdx
	mov rdx, QWORD PTR [rdi+104]
	and rdx, rax
	mov QWORD PTR [rdi+2728], rdx
	mov rdx, QWORD PTR [rdi+112]
	and rdx, rax
	mov QWORD PTR [rdi+2736], rdx
	mov rdx, QWORD PTR [rdi+120]
	and rdx, rax
	mov QWORD PTR [rdi+2744], rdx
	mov r8, QWORD PTR [rdi+192]
	add r8, QWORD PTR [rdi+2688]
	mov QWORD PTR [rdi+2688], r8
	mov r8, QWORD PTR [rdi+200]
	adc r8, QWORD PTR [rdi+2696]
	mov QWORD PTR [rdi+2696], r8
	mov r8, QWORD PTR [rdi+208]
	adc r8, QWORD PTR [rdi+2704]
	mov QWORD PTR [rdi+2704], r8
	mov r8, QWORD PTR [rdi+216]
	adc r8, QWORD PTR [rdi+2712]
	mov QWORD PTR [rdi+2712], r8
	mov r8, QWORD PTR [rdi+224]
	adc r8, QWORD PTR [rdi+2720]
	mov QWORD PTR [rdi+2720], r8
	mov r8, QWORD PTR [rdi+232]
	adc r8, QWORD PTR [rdi+2728]
	mov QWORD PTR [rdi+2728], r8
	mov r8, QWORD PTR [rdi+240]
	adc r8, QWORD PTR [rdi+2736]
	mov QWORD PTR [rdi+2736], r8
	mov r8, QWORD PTR [rdi+248]
	adc r8, QWORD PTR [rdi+2744]
	mov QWORD PTR [rdi+2744], r8
	mov rdx, QWORD PTR [rdi+2688]
	or rdx, QWORD PTR [rdi+2696]
	or rdx, QWORD PTR [rdi+2704]
	or rdx, QWORD PTR [rdi+2712]
	or rdx, QWORD PTR [rdi+2720]
	or rdx, QWORD PTR [rdi+2728]
	or rdx, QWORD PTR [rdi+2736]
	or rdx, QWORD PTR [rdi+2744]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2880]
	and rax, rdx
	mov QWORD PTR [rdi+2880], rax
	mov rcx, QWORD PTR [rdi+2880]
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+2240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2496], rax
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+2248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2504], rax
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+2256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2512], rax
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+2264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2520], rax
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+2272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2528], rax
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+2280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2536], rax
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+2288]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2544], rax
	mov rax, QWORD PTR [rdi+632]
	mov rdx, QWORD PTR [rdi+2296]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2552], rax
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+2304]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2816], rax
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+2312]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2824], rax
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+2320]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2832], rax
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+2328]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2840], rax
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+2336]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2848], rax
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+2344]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2856], rax
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+2352]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2864], rax
	mov rax, QWORD PTR [rdi+696]
	mov rdx, QWORD PTR [rdi+2360]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+2872], rax
	movq rbx, xmm0
	movq rbp, xmm1
	movq r12, xmm2
	movq r13, xmm3
	movq r14, xmm4
	movq r15, xmm5
	ret
	.p2align 6
