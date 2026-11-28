// The functions of `src/internal/vg_slhdsa_shake_xmss_192s_avx512vl.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_xmss_192s_avx512vl:
	mov QWORD PTR [rdi+2528], rbx
	mov QWORD PTR [rdi+2536], rbp
	mov QWORD PTR [rdi+2544], r12
	mov QWORD PTR [rdi+2552], r13
	mov QWORD PTR [rdi+2560], r14
	mov QWORD PTR [rdi+2568], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rdx
	mov r15, rdi
	add r15, 30496
	mov r10d, 0
	movzx eax, BYTE PTR [r15]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30368], al
	and rcx, 15
	mov BYTE PTR [rbx+30369], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+1]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30370], al
	and rcx, 15
	mov BYTE PTR [rbx+30371], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+2]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30372], al
	and rcx, 15
	mov BYTE PTR [rbx+30373], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+3]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30374], al
	and rcx, 15
	mov BYTE PTR [rbx+30375], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+4]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30376], al
	and rcx, 15
	mov BYTE PTR [rbx+30377], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+5]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30378], al
	and rcx, 15
	mov BYTE PTR [rbx+30379], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+6]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30380], al
	and rcx, 15
	mov BYTE PTR [rbx+30381], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+7]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30382], al
	and rcx, 15
	mov BYTE PTR [rbx+30383], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+8]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30384], al
	and rcx, 15
	mov BYTE PTR [rbx+30385], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+9]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30386], al
	and rcx, 15
	mov BYTE PTR [rbx+30387], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+10]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30388], al
	and rcx, 15
	mov BYTE PTR [rbx+30389], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+11]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30390], al
	and rcx, 15
	mov BYTE PTR [rbx+30391], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+12]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30392], al
	and rcx, 15
	mov BYTE PTR [rbx+30393], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+13]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30394], al
	and rcx, 15
	mov BYTE PTR [rbx+30395], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+14]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30396], al
	and rcx, 15
	mov BYTE PTR [rbx+30397], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+15]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30398], al
	and rcx, 15
	mov BYTE PTR [rbx+30399], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+16]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30400], al
	and rcx, 15
	mov BYTE PTR [rbx+30401], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+17]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30402], al
	and rcx, 15
	mov BYTE PTR [rbx+30403], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+18]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30404], al
	and rcx, 15
	mov BYTE PTR [rbx+30405], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+19]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30406], al
	and rcx, 15
	mov BYTE PTR [rbx+30407], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+20]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30408], al
	and rcx, 15
	mov BYTE PTR [rbx+30409], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+21]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30410], al
	and rcx, 15
	mov BYTE PTR [rbx+30411], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+22]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30412], al
	and rcx, 15
	mov BYTE PTR [rbx+30413], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+23]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30414], al
	and rcx, 15
	mov BYTE PTR [rbx+30415], cl
	add r10, rax
	add r10, rcx
	mov r11d, 720
	sub r11, r10
	mov rax, r11
	shr rax, 8
	and rax, 15
	mov BYTE PTR [rbx+30416], al
	mov rax, r11
	shr rax, 4
	and rax, 15
	mov BYTE PTR [rbx+30417], al
	mov rax, r11
	and rax, 15
	mov BYTE PTR [rbx+30418], al
	mov eax, 0
	mov QWORD PTR [rbx+2576], rax
	mov QWORD PTR [rbx+2584], rax
20:
	mov rdi, rbx
	mov rsi, QWORD PTR [rbx+2576]
	mov rdx, r12
	mov rcx, r13
	call {vg_slhdsa_shake_wots4_n24_avx512vl}
	mov rax, QWORD PTR [rbx+2576]
	add rax, 4
	mov QWORD PTR [rbx+2576], rax
	cmp rax, 512
	jne 20b
	mov r10, r13
	add r10, 1224
	mov eax, 0
	mov QWORD PTR [r10], rax
	mov QWORD PTR [r10+8], rax
	mov QWORD PTR [r10+16], rax
	mov QWORD PTR [r10+24], rax
	mov QWORD PTR [r10+32], rax
	mov QWORD PTR [r10+40], rax
	mov QWORD PTR [r10+48], rax
	mov QWORD PTR [r10+56], rax
	mov QWORD PTR [r10+64], rax
	mov QWORD PTR [r10+72], rax
	mov QWORD PTR [r10+80], rax
	mov QWORD PTR [r10+88], rax
	mov QWORD PTR [r10+96], rax
	mov QWORD PTR [r10+104], rax
	mov QWORD PTR [r10+112], rax
	mov QWORD PTR [r10+120], rax
	mov QWORD PTR [r10+128], rax
	mov QWORD PTR [r10+136], rax
	mov QWORD PTR [r10+144], rax
	mov QWORD PTR [r10+152], rax
	mov QWORD PTR [r10+160], rax
	mov QWORD PTR [r10+168], rax
	mov QWORD PTR [r10+176], rax
	mov QWORD PTR [r10+184], rax
	mov QWORD PTR [r10+192], rax
	mov QWORD PTR [r10+200], rax
	mov QWORD PTR [r10+208], rax
	mov rax, 0
	mov QWORD PTR [rbx+3000], rax
	mov rax, 0
	mov QWORD PTR [rbx+3008], rax
	mov rax, 2
	mov QWORD PTR [rbx+3016], rax
	mov rax, 0
	mov QWORD PTR [rbx+3024], rax
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 12640
	mov edx, 512
	mov ecx, 0
	mov r8, r10
	mov r9, r12
	call {vg_slhdsa_shake_levels_n24_avx512vl}
	mov rax, QWORD PTR [rbx+12640]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rbx+12648]
	mov QWORD PTR [r15+8], rax
	mov rax, QWORD PTR [rbx+12656]
	mov QWORD PTR [r15+16], rax
	mov r15, QWORD PTR [rbx+2568]
	mov r14, QWORD PTR [rbx+2560]
	mov r13, QWORD PTR [rbx+2552]
	mov r12, QWORD PTR [rbx+2544]
	mov rbp, QWORD PTR [rbx+2536]
	mov rbx, QWORD PTR [rbx+2528]
	ret
	.p2align 6
