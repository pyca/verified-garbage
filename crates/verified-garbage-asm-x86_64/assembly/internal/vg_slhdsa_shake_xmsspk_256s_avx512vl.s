// The functions of `src/internal/vg_slhdsa_shake_xmsspk_256s_avx512vl.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_xmsspk_256s_avx512vl:
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
	mov r14, r15
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
	movzx eax, BYTE PTR [r15+24]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30416], al
	and rcx, 15
	mov BYTE PTR [rbx+30417], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+25]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30418], al
	and rcx, 15
	mov BYTE PTR [rbx+30419], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+26]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30420], al
	and rcx, 15
	mov BYTE PTR [rbx+30421], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+27]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30422], al
	and rcx, 15
	mov BYTE PTR [rbx+30423], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+28]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30424], al
	and rcx, 15
	mov BYTE PTR [rbx+30425], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+29]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30426], al
	and rcx, 15
	mov BYTE PTR [rbx+30427], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+30]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30428], al
	and rcx, 15
	mov BYTE PTR [rbx+30429], cl
	add r10, rax
	add r10, rcx
	movzx eax, BYTE PTR [r15+31]
	mov rcx, rax
	shr rax, 4
	mov BYTE PTR [rbx+30430], al
	and rcx, 15
	mov BYTE PTR [rbx+30431], cl
	add r10, rax
	add r10, rcx
	mov r11d, 960
	sub r11, r10
	mov rax, r11
	shr rax, 8
	and rax, 15
	mov BYTE PTR [rbx+30432], al
	mov rax, r11
	shr rax, 4
	and rax, 15
	mov BYTE PTR [rbx+30433], al
	mov rax, r11
	and rax, 15
	mov BYTE PTR [rbx+30434], al
	mov eax, 0
	mov QWORD PTR [rbx+2576], rax
	mov QWORD PTR [rbx+2584], rax
	mov eax, 0
	mov QWORD PTR [rbx+2576], rax
20:
	mov eax, 15
	mov QWORD PTR [rbx+2592], rax
	mov r10, QWORD PTR [rbx+2576]
	add r10, 0
	mov eax, 66
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 66
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	movzx r11d, BYTE PTR [rbx+r10*1+30368]
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3344], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3348], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3352], eax
	mov rsi, r10
	shl rsi, 5
	add rsi, r13
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3360], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3368], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3376], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3384], rax
	mov rax, QWORD PTR [rbx+2592]
	sub rax, r11
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov rax, r11
	xor rax, QWORD PTR [rbx+2592]
	and rax, rdx
	xor rax, r11
	mov QWORD PTR [rbx+2592], rax
	mov r10, QWORD PTR [rbx+2576]
	add r10, 1
	mov eax, 66
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 66
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	movzx r11d, BYTE PTR [rbx+r10*1+30368]
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3472], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3476], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3480], eax
	mov rsi, r10
	shl rsi, 5
	add rsi, r13
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3488], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3496], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3504], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3512], rax
	mov rax, QWORD PTR [rbx+2592]
	sub rax, r11
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov rax, r11
	xor rax, QWORD PTR [rbx+2592]
	and rax, rdx
	xor rax, r11
	mov QWORD PTR [rbx+2592], rax
	mov r10, QWORD PTR [rbx+2576]
	add r10, 2
	mov eax, 66
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 66
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	movzx r11d, BYTE PTR [rbx+r10*1+30368]
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3600], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3604], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3608], eax
	mov rsi, r10
	shl rsi, 5
	add rsi, r13
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3616], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3624], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3632], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3640], rax
	mov rax, QWORD PTR [rbx+2592]
	sub rax, r11
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov rax, r11
	xor rax, QWORD PTR [rbx+2592]
	and rax, rdx
	xor rax, r11
	mov QWORD PTR [rbx+2592], rax
	mov r10, QWORD PTR [rbx+2576]
	add r10, 3
	mov eax, 66
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 66
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	movzx r11d, BYTE PTR [rbx+r10*1+30368]
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3728], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3732], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3736], eax
	mov rsi, r10
	shl rsi, 5
	add rsi, r13
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3744], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3752], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3760], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3768], rax
	mov rax, QWORD PTR [rbx+2592]
	sub rax, r11
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	mov rax, r11
	xor rax, QWORD PTR [rbx+2592]
	and rax, rdx
	xor rax, r11
	mov QWORD PTR [rbx+2592], rax
	mov rax, QWORD PTR [rbx+2592]
	mov QWORD PTR [rbx+2584], rax
	cmp rax, 15
	jb 21f
	jmp 22f
21:
23:
	mov r10, QWORD PTR [rbx+2584]
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3356], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3484], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3612], eax
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3740], eax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 96
	mov rcx, rdi
	add rcx, 64
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n32_avx512vl}
	mov r10, QWORD PTR [rbx+2576]
	add r10, 0
	mov eax, 66
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 66
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	movzx r11d, BYTE PTR [rbx+r10*1+30368]
	cmp r11, QWORD PTR [rbx+2584]
	je 24f
	jb 26f
	mov rsi, r10
	shl rsi, 5
	add rsi, r13
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3360], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3368], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3376], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3384], rax
	jmp 27f
26:
27:
	jmp 25f
24:
25:
	mov r10, QWORD PTR [rbx+2576]
	add r10, 1
	mov eax, 66
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 66
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	movzx r11d, BYTE PTR [rbx+r10*1+30368]
	cmp r11, QWORD PTR [rbx+2584]
	je 28f
	jb 210f
	mov rsi, r10
	shl rsi, 5
	add rsi, r13
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3488], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3496], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3504], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3512], rax
	jmp 211f
210:
211:
	jmp 29f
28:
29:
	mov r10, QWORD PTR [rbx+2576]
	add r10, 2
	mov eax, 66
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 66
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	movzx r11d, BYTE PTR [rbx+r10*1+30368]
	cmp r11, QWORD PTR [rbx+2584]
	je 212f
	jb 214f
	mov rsi, r10
	shl rsi, 5
	add rsi, r13
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3616], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3624], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3632], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3640], rax
	jmp 215f
214:
215:
	jmp 213f
212:
213:
	mov r10, QWORD PTR [rbx+2576]
	add r10, 3
	mov eax, 66
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 66
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	movzx r11d, BYTE PTR [rbx+r10*1+30368]
	cmp r11, QWORD PTR [rbx+2584]
	je 216f
	jb 218f
	mov rsi, r10
	shl rsi, 5
	add rsi, r13
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3744], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3752], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3760], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3768], rax
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	mov rax, QWORD PTR [rbx+2584]
	add rax, 1
	mov QWORD PTR [rbx+2584], rax
	cmp rax, 15
	jne 23b
22:
	mov r10, QWORD PTR [rbx+2576]
	add r10, 0
	mov eax, 66
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 66
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	movzx r11d, BYTE PTR [rbx+r10*1+30368]
	mov rdx, r10
	shl rdx, 5
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3360]
	mov QWORD PTR [rdx+3872], rax
	mov rax, QWORD PTR [rbx+3368]
	mov QWORD PTR [rdx+3880], rax
	mov rax, QWORD PTR [rbx+3376]
	mov QWORD PTR [rdx+3888], rax
	mov rax, QWORD PTR [rbx+3384]
	mov QWORD PTR [rdx+3896], rax
	mov r10, QWORD PTR [rbx+2576]
	add r10, 1
	mov eax, 66
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 66
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	movzx r11d, BYTE PTR [rbx+r10*1+30368]
	mov rdx, r10
	shl rdx, 5
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3488]
	mov QWORD PTR [rdx+3872], rax
	mov rax, QWORD PTR [rbx+3496]
	mov QWORD PTR [rdx+3880], rax
	mov rax, QWORD PTR [rbx+3504]
	mov QWORD PTR [rdx+3888], rax
	mov rax, QWORD PTR [rbx+3512]
	mov QWORD PTR [rdx+3896], rax
	mov r10, QWORD PTR [rbx+2576]
	add r10, 2
	mov eax, 66
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 66
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	movzx r11d, BYTE PTR [rbx+r10*1+30368]
	mov rdx, r10
	shl rdx, 5
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3616]
	mov QWORD PTR [rdx+3872], rax
	mov rax, QWORD PTR [rbx+3624]
	mov QWORD PTR [rdx+3880], rax
	mov rax, QWORD PTR [rbx+3632]
	mov QWORD PTR [rdx+3888], rax
	mov rax, QWORD PTR [rbx+3640]
	mov QWORD PTR [rdx+3896], rax
	mov r10, QWORD PTR [rbx+2576]
	add r10, 3
	mov eax, 66
	sub rax, r10
	shr rax, 63
	mov rcx, r10
	sub rcx, 66
	mov edx, 0
	sub rdx, rax
	and rcx, rdx
	sub r10, rcx
	movzx r11d, BYTE PTR [rbx+r10*1+30368]
	mov rdx, r10
	shl rdx, 5
	add rdx, rbx
	mov rax, QWORD PTR [rbx+3744]
	mov QWORD PTR [rdx+3872], rax
	mov rax, QWORD PTR [rbx+3752]
	mov QWORD PTR [rdx+3880], rax
	mov rax, QWORD PTR [rbx+3760]
	mov QWORD PTR [rdx+3888], rax
	mov rax, QWORD PTR [rbx+3768]
	mov QWORD PTR [rdx+3896], rax
	mov rax, QWORD PTR [rbx+2576]
	add rax, 4
	mov QWORD PTR [rbx+2576], rax
	cmp rax, 67
	jb 20b
	mov eax, 1
	bswap eax
	mov DWORD PTR [rbx+3856], eax
	mov eax, r12d
	bswap eax
	mov DWORD PTR [rbx+3860], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3864], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3868], eax
	mov rdi, rbx
	add rdi, 3808
	mov esi, 2208
	mov edx, 2208
	mov rcx, rdi
	add rcx, 64
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n32_avx512vl}
	mov rax, QWORD PTR [rbx+3872]
	mov QWORD PTR [rbx+3360], rax
	mov rax, QWORD PTR [rbx+3880]
	mov QWORD PTR [rbx+3368], rax
	mov rax, QWORD PTR [rbx+3888]
	mov QWORD PTR [rbx+3376], rax
	mov rax, QWORD PTR [rbx+3896]
	mov QWORD PTR [rbx+3384], rax
	mov eax, 0
	mov QWORD PTR [rbx+2600], rax
220:
	mov rcx, QWORD PTR [rbx+2600]
	mov rax, r12
	shr rax, cl
	mov rsi, rcx
	shl rsi, 5
	add rsi, r13
	add rsi, 2144
	and rax, 1
	je 221f
	mov rax, QWORD PTR [rbx+3360]
	mov QWORD PTR [rbx+3392], rax
	mov rax, QWORD PTR [rbx+3368]
	mov QWORD PTR [rbx+3400], rax
	mov rax, QWORD PTR [rbx+3376]
	mov QWORD PTR [rbx+3408], rax
	mov rax, QWORD PTR [rbx+3384]
	mov QWORD PTR [rbx+3416], rax
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3360], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3368], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3376], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3384], rax
	jmp 222f
221:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rbx+3392], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [rbx+3400], rax
	mov rax, QWORD PTR [rsi+16]
	mov QWORD PTR [rbx+3408], rax
	mov rax, QWORD PTR [rsi+24]
	mov QWORD PTR [rbx+3416], rax
222:
	mov eax, 2
	bswap eax
	mov DWORD PTR [rbx+3344], eax
	mov eax, 0
	bswap eax
	mov DWORD PTR [rbx+3348], eax
	mov r10, QWORD PTR [rbx+2600]
	add r10, 1
	mov eax, r10d
	bswap eax
	mov DWORD PTR [rbx+3352], eax
	mov rcx, r10
	mov r11, r12
	shr r11, cl
	mov eax, r11d
	bswap eax
	mov DWORD PTR [rbx+3356], eax
	mov rdi, rbx
	add rdi, 3296
	mov esi, 128
	mov edx, 128
	mov rcx, rdi
	add rcx, 64
	mov r8, rbx
	call {vg_slhdsa_shake_thash4_n32_avx512vl}
	mov rax, QWORD PTR [rbx+2600]
	add rax, 1
	mov QWORD PTR [rbx+2600], rax
	cmp rax, 8
	jne 220b
	mov rax, QWORD PTR [rbx+3360]
	mov QWORD PTR [r14], rax
	mov rax, QWORD PTR [rbx+3368]
	mov QWORD PTR [r14+8], rax
	mov rax, QWORD PTR [rbx+3376]
	mov QWORD PTR [r14+16], rax
	mov rax, QWORD PTR [rbx+3384]
	mov QWORD PTR [r14+24], rax
	mov r15, QWORD PTR [rbx+2568]
	mov r14, QWORD PTR [rbx+2560]
	mov r13, QWORD PTR [rbx+2552]
	mov r12, QWORD PTR [rbx+2544]
	mov rbp, QWORD PTR [rbx+2536]
	mov rbx, QWORD PTR [rbx+2528]
	ret
	.p2align 6
