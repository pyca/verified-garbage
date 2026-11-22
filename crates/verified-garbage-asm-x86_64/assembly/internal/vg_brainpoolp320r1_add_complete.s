// The functions of `src/internal/vg_brainpoolp320r1_add_complete.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_add_complete:
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+624]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+632]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+640]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+648]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+656]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+984], r13
	mov QWORD PTR [rdi+992], r14
	mov QWORD PTR [rdi+1000], r8
	mov QWORD PTR [rdi+1008], r9
	mov QWORD PTR [rdi+1016], r10
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+664]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+672]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+680]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+688]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+696]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1024], r13
	mov QWORD PTR [rdi+1032], r14
	mov QWORD PTR [rdi+1040], r8
	mov QWORD PTR [rdi+1048], r9
	mov QWORD PTR [rdi+1056], r10
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+704]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+712]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+720]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+728]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+736]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1064], r13
	mov QWORD PTR [rdi+1072], r14
	mov QWORD PTR [rdi+1080], r8
	mov QWORD PTR [rdi+1088], r9
	mov QWORD PTR [rdi+1096], r10
	mov r8, QWORD PTR [rdi+624]
	mov r9, QWORD PTR [rdi+632]
	mov r10, QWORD PTR [rdi+640]
	mov r11, QWORD PTR [rdi+648]
	mov r12, QWORD PTR [rdi+656]
	mov r13d, 0
	add r8, QWORD PTR [rdi+664]
	adc r9, QWORD PTR [rdi+672]
	adc r10, QWORD PTR [rdi+680]
	adc r11, QWORD PTR [rdi+688]
	adc r12, QWORD PTR [rdi+696]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1104], r8
	mov QWORD PTR [rdi+1112], r9
	mov QWORD PTR [rdi+1120], r10
	mov QWORD PTR [rdi+1128], r11
	mov QWORD PTR [rdi+1136], r12
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	mov r12, QWORD PTR [rdi+896]
	mov r13d, 0
	add r8, QWORD PTR [rdi+904]
	adc r9, QWORD PTR [rdi+912]
	adc r10, QWORD PTR [rdi+920]
	adc r11, QWORD PTR [rdi+928]
	adc r12, QWORD PTR [rdi+936]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1144], r8
	mov QWORD PTR [rdi+1152], r9
	mov QWORD PTR [rdi+1160], r10
	mov QWORD PTR [rdi+1168], r11
	mov QWORD PTR [rdi+1176], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+1104]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+1112]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1120]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1128]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1136]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1104], r13
	mov QWORD PTR [rdi+1112], r14
	mov QWORD PTR [rdi+1120], r8
	mov QWORD PTR [rdi+1128], r9
	mov QWORD PTR [rdi+1136], r10
	mov r8, QWORD PTR [rdi+984]
	mov r9, QWORD PTR [rdi+992]
	mov r10, QWORD PTR [rdi+1000]
	mov r11, QWORD PTR [rdi+1008]
	mov r12, QWORD PTR [rdi+1016]
	mov r13d, 0
	add r8, QWORD PTR [rdi+1024]
	adc r9, QWORD PTR [rdi+1032]
	adc r10, QWORD PTR [rdi+1040]
	adc r11, QWORD PTR [rdi+1048]
	adc r12, QWORD PTR [rdi+1056]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1144], r8
	mov QWORD PTR [rdi+1152], r9
	mov QWORD PTR [rdi+1160], r10
	mov QWORD PTR [rdi+1168], r11
	mov QWORD PTR [rdi+1176], r12
	mov r8, QWORD PTR [rdi+1104]
	mov r9, QWORD PTR [rdi+1112]
	mov r10, QWORD PTR [rdi+1120]
	mov r11, QWORD PTR [rdi+1128]
	mov r12, QWORD PTR [rdi+1136]
	sub r8, QWORD PTR [rdi+1144]
	sbb r9, QWORD PTR [rdi+1152]
	sbb r10, QWORD PTR [rdi+1160]
	sbb r11, QWORD PTR [rdi+1168]
	sbb r12, QWORD PTR [rdi+1176]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+160], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+168], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+176], rdx
	add r8, QWORD PTR [rdi+144]
	adc r9, QWORD PTR [rdi+152]
	adc r10, QWORD PTR [rdi+160]
	adc r11, QWORD PTR [rdi+168]
	adc r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1104], r8
	mov QWORD PTR [rdi+1112], r9
	mov QWORD PTR [rdi+1120], r10
	mov QWORD PTR [rdi+1128], r11
	mov QWORD PTR [rdi+1136], r12
	mov r8, QWORD PTR [rdi+624]
	mov r9, QWORD PTR [rdi+632]
	mov r10, QWORD PTR [rdi+640]
	mov r11, QWORD PTR [rdi+648]
	mov r12, QWORD PTR [rdi+656]
	mov r13d, 0
	add r8, QWORD PTR [rdi+704]
	adc r9, QWORD PTR [rdi+712]
	adc r10, QWORD PTR [rdi+720]
	adc r11, QWORD PTR [rdi+728]
	adc r12, QWORD PTR [rdi+736]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1144], r8
	mov QWORD PTR [rdi+1152], r9
	mov QWORD PTR [rdi+1160], r10
	mov QWORD PTR [rdi+1168], r11
	mov QWORD PTR [rdi+1176], r12
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	mov r12, QWORD PTR [rdi+896]
	mov r13d, 0
	add r8, QWORD PTR [rdi+944]
	adc r9, QWORD PTR [rdi+952]
	adc r10, QWORD PTR [rdi+960]
	adc r11, QWORD PTR [rdi+968]
	adc r12, QWORD PTR [rdi+976]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov QWORD PTR [rdi+1216], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+1144]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1144], r13
	mov QWORD PTR [rdi+1152], r14
	mov QWORD PTR [rdi+1160], r8
	mov QWORD PTR [rdi+1168], r9
	mov QWORD PTR [rdi+1176], r10
	mov r8, QWORD PTR [rdi+984]
	mov r9, QWORD PTR [rdi+992]
	mov r10, QWORD PTR [rdi+1000]
	mov r11, QWORD PTR [rdi+1008]
	mov r12, QWORD PTR [rdi+1016]
	mov r13d, 0
	add r8, QWORD PTR [rdi+1064]
	adc r9, QWORD PTR [rdi+1072]
	adc r10, QWORD PTR [rdi+1080]
	adc r11, QWORD PTR [rdi+1088]
	adc r12, QWORD PTR [rdi+1096]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov QWORD PTR [rdi+1216], r12
	mov r8, QWORD PTR [rdi+1144]
	mov r9, QWORD PTR [rdi+1152]
	mov r10, QWORD PTR [rdi+1160]
	mov r11, QWORD PTR [rdi+1168]
	mov r12, QWORD PTR [rdi+1176]
	sub r8, QWORD PTR [rdi+1184]
	sbb r9, QWORD PTR [rdi+1192]
	sbb r10, QWORD PTR [rdi+1200]
	sbb r11, QWORD PTR [rdi+1208]
	sbb r12, QWORD PTR [rdi+1216]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+160], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+168], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+176], rdx
	add r8, QWORD PTR [rdi+144]
	adc r9, QWORD PTR [rdi+152]
	adc r10, QWORD PTR [rdi+160]
	adc r11, QWORD PTR [rdi+168]
	adc r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1144], r8
	mov QWORD PTR [rdi+1152], r9
	mov QWORD PTR [rdi+1160], r10
	mov QWORD PTR [rdi+1168], r11
	mov QWORD PTR [rdi+1176], r12
	mov r8, QWORD PTR [rdi+664]
	mov r9, QWORD PTR [rdi+672]
	mov r10, QWORD PTR [rdi+680]
	mov r11, QWORD PTR [rdi+688]
	mov r12, QWORD PTR [rdi+696]
	mov r13d, 0
	add r8, QWORD PTR [rdi+704]
	adc r9, QWORD PTR [rdi+712]
	adc r10, QWORD PTR [rdi+720]
	adc r11, QWORD PTR [rdi+728]
	adc r12, QWORD PTR [rdi+736]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov QWORD PTR [rdi+1216], r12
	mov r8, QWORD PTR [rdi+904]
	mov r9, QWORD PTR [rdi+912]
	mov r10, QWORD PTR [rdi+920]
	mov r11, QWORD PTR [rdi+928]
	mov r12, QWORD PTR [rdi+936]
	mov r13d, 0
	add r8, QWORD PTR [rdi+944]
	adc r9, QWORD PTR [rdi+952]
	adc r10, QWORD PTR [rdi+960]
	adc r11, QWORD PTR [rdi+968]
	adc r12, QWORD PTR [rdi+976]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+744], r8
	mov QWORD PTR [rdi+752], r9
	mov QWORD PTR [rdi+760], r10
	mov QWORD PTR [rdi+768], r11
	mov QWORD PTR [rdi+776], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1184], r13
	mov QWORD PTR [rdi+1192], r14
	mov QWORD PTR [rdi+1200], r8
	mov QWORD PTR [rdi+1208], r9
	mov QWORD PTR [rdi+1216], r10
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13d, 0
	add r8, QWORD PTR [rdi+1064]
	adc r9, QWORD PTR [rdi+1072]
	adc r10, QWORD PTR [rdi+1080]
	adc r11, QWORD PTR [rdi+1088]
	adc r12, QWORD PTR [rdi+1096]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+744], r8
	mov QWORD PTR [rdi+752], r9
	mov QWORD PTR [rdi+760], r10
	mov QWORD PTR [rdi+768], r11
	mov QWORD PTR [rdi+776], r12
	mov r8, QWORD PTR [rdi+1184]
	mov r9, QWORD PTR [rdi+1192]
	mov r10, QWORD PTR [rdi+1200]
	mov r11, QWORD PTR [rdi+1208]
	mov r12, QWORD PTR [rdi+1216]
	sub r8, QWORD PTR [rdi+744]
	sbb r9, QWORD PTR [rdi+752]
	sbb r10, QWORD PTR [rdi+760]
	sbb r11, QWORD PTR [rdi+768]
	sbb r12, QWORD PTR [rdi+776]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+160], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+168], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+176], rdx
	add r8, QWORD PTR [rdi+144]
	adc r9, QWORD PTR [rdi+152]
	adc r10, QWORD PTR [rdi+160]
	adc r11, QWORD PTR [rdi+168]
	adc r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1184], r8
	mov QWORD PTR [rdi+1192], r9
	mov QWORD PTR [rdi+1200], r10
	mov QWORD PTR [rdi+1208], r11
	mov QWORD PTR [rdi+1216], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+304]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+312]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+824], r13
	mov QWORD PTR [rdi+832], r14
	mov QWORD PTR [rdi+840], r8
	mov QWORD PTR [rdi+848], r9
	mov QWORD PTR [rdi+856], r10
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+1264]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+1272]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+744], r13
	mov QWORD PTR [rdi+752], r14
	mov QWORD PTR [rdi+760], r8
	mov QWORD PTR [rdi+768], r9
	mov QWORD PTR [rdi+776], r10
	mov r8, QWORD PTR [rdi+744]
	mov r9, QWORD PTR [rdi+752]
	mov r10, QWORD PTR [rdi+760]
	mov r11, QWORD PTR [rdi+768]
	mov r12, QWORD PTR [rdi+776]
	mov r13d, 0
	add r8, QWORD PTR [rdi+824]
	adc r9, QWORD PTR [rdi+832]
	adc r10, QWORD PTR [rdi+840]
	adc r11, QWORD PTR [rdi+848]
	adc r12, QWORD PTR [rdi+856]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+824], r8
	mov QWORD PTR [rdi+832], r9
	mov QWORD PTR [rdi+840], r10
	mov QWORD PTR [rdi+848], r11
	mov QWORD PTR [rdi+856], r12
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	sub r8, QWORD PTR [rdi+824]
	sbb r9, QWORD PTR [rdi+832]
	sbb r10, QWORD PTR [rdi+840]
	sbb r11, QWORD PTR [rdi+848]
	sbb r12, QWORD PTR [rdi+856]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+160], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+168], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+176], rdx
	add r8, QWORD PTR [rdi+144]
	adc r9, QWORD PTR [rdi+152]
	adc r10, QWORD PTR [rdi+160]
	adc r11, QWORD PTR [rdi+168]
	adc r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+744], r8
	mov QWORD PTR [rdi+752], r9
	mov QWORD PTR [rdi+760], r10
	mov QWORD PTR [rdi+768], r11
	mov QWORD PTR [rdi+776], r12
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13d, 0
	add r8, QWORD PTR [rdi+824]
	adc r9, QWORD PTR [rdi+832]
	adc r10, QWORD PTR [rdi+840]
	adc r11, QWORD PTR [rdi+848]
	adc r12, QWORD PTR [rdi+856]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+824], r8
	mov QWORD PTR [rdi+832], r9
	mov QWORD PTR [rdi+840], r10
	mov QWORD PTR [rdi+848], r11
	mov QWORD PTR [rdi+856], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+744]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+752]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+760]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+768]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+776]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+784], r13
	mov QWORD PTR [rdi+792], r14
	mov QWORD PTR [rdi+800], r8
	mov QWORD PTR [rdi+808], r9
	mov QWORD PTR [rdi+816], r10
	mov r8, QWORD PTR [rdi+984]
	mov r9, QWORD PTR [rdi+992]
	mov r10, QWORD PTR [rdi+1000]
	mov r11, QWORD PTR [rdi+1008]
	mov r12, QWORD PTR [rdi+1016]
	mov r13d, 0
	add r8, QWORD PTR [rdi+984]
	adc r9, QWORD PTR [rdi+992]
	adc r10, QWORD PTR [rdi+1000]
	adc r11, QWORD PTR [rdi+1008]
	adc r12, QWORD PTR [rdi+1016]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov QWORD PTR [rdi+1056], r12
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13d, 0
	add r8, QWORD PTR [rdi+984]
	adc r9, QWORD PTR [rdi+992]
	adc r10, QWORD PTR [rdi+1000]
	adc r11, QWORD PTR [rdi+1008]
	adc r12, QWORD PTR [rdi+1016]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov QWORD PTR [rdi+1056], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+304]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+312]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1064], r13
	mov QWORD PTR [rdi+1072], r14
	mov QWORD PTR [rdi+1080], r8
	mov QWORD PTR [rdi+1088], r9
	mov QWORD PTR [rdi+1096], r10
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+1264]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+1272]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1144], r13
	mov QWORD PTR [rdi+1152], r14
	mov QWORD PTR [rdi+1160], r8
	mov QWORD PTR [rdi+1168], r9
	mov QWORD PTR [rdi+1176], r10
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13d, 0
	add r8, QWORD PTR [rdi+1064]
	adc r9, QWORD PTR [rdi+1072]
	adc r10, QWORD PTR [rdi+1080]
	adc r11, QWORD PTR [rdi+1088]
	adc r12, QWORD PTR [rdi+1096]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov QWORD PTR [rdi+1056], r12
	mov r8, QWORD PTR [rdi+984]
	mov r9, QWORD PTR [rdi+992]
	mov r10, QWORD PTR [rdi+1000]
	mov r11, QWORD PTR [rdi+1008]
	mov r12, QWORD PTR [rdi+1016]
	sub r8, QWORD PTR [rdi+1064]
	sbb r9, QWORD PTR [rdi+1072]
	sbb r10, QWORD PTR [rdi+1080]
	sbb r11, QWORD PTR [rdi+1088]
	sbb r12, QWORD PTR [rdi+1096]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+160], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+168], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+176], rdx
	add r8, QWORD PTR [rdi+144]
	adc r9, QWORD PTR [rdi+152]
	adc r10, QWORD PTR [rdi+160]
	adc r11, QWORD PTR [rdi+168]
	adc r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1064], r8
	mov QWORD PTR [rdi+1072], r9
	mov QWORD PTR [rdi+1080], r10
	mov QWORD PTR [rdi+1088], r11
	mov QWORD PTR [rdi+1096], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+304]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+312]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1064]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1064], r13
	mov QWORD PTR [rdi+1072], r14
	mov QWORD PTR [rdi+1080], r8
	mov QWORD PTR [rdi+1088], r9
	mov QWORD PTR [rdi+1096], r10
	mov r8, QWORD PTR [rdi+1144]
	mov r9, QWORD PTR [rdi+1152]
	mov r10, QWORD PTR [rdi+1160]
	mov r11, QWORD PTR [rdi+1168]
	mov r12, QWORD PTR [rdi+1176]
	mov r13d, 0
	add r8, QWORD PTR [rdi+1064]
	adc r9, QWORD PTR [rdi+1072]
	adc r10, QWORD PTR [rdi+1080]
	adc r11, QWORD PTR [rdi+1088]
	adc r12, QWORD PTR [rdi+1096]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+1144], r8
	mov QWORD PTR [rdi+1152], r9
	mov QWORD PTR [rdi+1160], r10
	mov QWORD PTR [rdi+1168], r11
	mov QWORD PTR [rdi+1176], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+1024]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+1032]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1040]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1048]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1056]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+984], r13
	mov QWORD PTR [rdi+992], r14
	mov QWORD PTR [rdi+1000], r8
	mov QWORD PTR [rdi+1008], r9
	mov QWORD PTR [rdi+1016], r10
	mov r8, QWORD PTR [rdi+784]
	mov r9, QWORD PTR [rdi+792]
	mov r10, QWORD PTR [rdi+800]
	mov r11, QWORD PTR [rdi+808]
	mov r12, QWORD PTR [rdi+816]
	mov r13d, 0
	add r8, QWORD PTR [rdi+984]
	adc r9, QWORD PTR [rdi+992]
	adc r10, QWORD PTR [rdi+1000]
	adc r11, QWORD PTR [rdi+1008]
	adc r12, QWORD PTR [rdi+1016]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+984], r13
	mov QWORD PTR [rdi+992], r14
	mov QWORD PTR [rdi+1000], r8
	mov QWORD PTR [rdi+1008], r9
	mov QWORD PTR [rdi+1016], r10
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+1104]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+1112]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1120]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1128]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1136]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+744], r13
	mov QWORD PTR [rdi+752], r14
	mov QWORD PTR [rdi+760], r8
	mov QWORD PTR [rdi+768], r9
	mov QWORD PTR [rdi+776], r10
	mov r8, QWORD PTR [rdi+744]
	mov r9, QWORD PTR [rdi+752]
	mov r10, QWORD PTR [rdi+760]
	mov r11, QWORD PTR [rdi+768]
	mov r12, QWORD PTR [rdi+776]
	sub r8, QWORD PTR [rdi+984]
	sbb r9, QWORD PTR [rdi+992]
	sbb r10, QWORD PTR [rdi+1000]
	sbb r11, QWORD PTR [rdi+1008]
	sbb r12, QWORD PTR [rdi+1016]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+160], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+168], rdx
	mov rdx, QWORD PTR [rdi+96]
	and rdx, rax
	mov QWORD PTR [rdi+176], rdx
	add r8, QWORD PTR [rdi+144]
	adc r9, QWORD PTR [rdi+152]
	adc r10, QWORD PTR [rdi+160]
	adc r11, QWORD PTR [rdi+168]
	adc r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+744], r8
	mov QWORD PTR [rdi+752], r9
	mov QWORD PTR [rdi+760], r10
	mov QWORD PTR [rdi+768], r11
	mov QWORD PTR [rdi+776], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+1104]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+1112]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1120]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1128]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1136]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1024]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1032]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1040]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1048]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1056]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+984], r13
	mov QWORD PTR [rdi+992], r14
	mov QWORD PTR [rdi+1000], r8
	mov QWORD PTR [rdi+1008], r9
	mov QWORD PTR [rdi+1016], r10
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rax, r8
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r14, 0
	mov rcx, QWORD PTR [rdi+1192]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rax, r9
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r8, 0
	mov rcx, QWORD PTR [rdi+1200]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r10, rax
	adc rdx, 0
	add r10, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1208]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r11, rax
	adc rdx, 0
	add r11, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r12
	movabs rcx, 4404128606415658601
	mul rcx
	mov rcx, rax
	mov ebp, 0
	mov rax, QWORD PTR [rdi+64]
	mul rcx
	add r12, rax
	adc rdx, 0
	add r12, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+72]
	mul rcx
	add r13, rax
	adc rdx, 0
	add r13, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+80]
	mul rcx
	add r14, rax
	adc rdx, 0
	add r14, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+88]
	mul rcx
	add r8, rax
	adc rdx, 0
	add r8, rbp
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add r9, rax
	adc rdx, 0
	add r9, rbp
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rax, r13
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r14
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r8
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r11
	sbb rax, 0
	cmovae r13, QWORD PTR [rdi+144]
	cmovae r14, QWORD PTR [rdi+152]
	cmovae r8, QWORD PTR [rdi+160]
	cmovae r9, QWORD PTR [rdi+168]
	cmovae r10, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+824], r13
	mov QWORD PTR [rdi+832], r14
	mov QWORD PTR [rdi+840], r8
	mov QWORD PTR [rdi+848], r9
	mov QWORD PTR [rdi+856], r10
	mov r8, QWORD PTR [rdi+824]
	mov r9, QWORD PTR [rdi+832]
	mov r10, QWORD PTR [rdi+840]
	mov r11, QWORD PTR [rdi+848]
	mov r12, QWORD PTR [rdi+856]
	mov r13d, 0
	add r8, QWORD PTR [rdi+984]
	adc r9, QWORD PTR [rdi+992]
	adc r10, QWORD PTR [rdi+1000]
	adc r11, QWORD PTR [rdi+1008]
	adc r12, QWORD PTR [rdi+1016]
	adc r13, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, r9
	sbb rax, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+152], rax
	mov rax, r10
	sbb rax, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+160], rax
	mov rax, r11
	sbb rax, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+168], rax
	mov rax, r12
	sbb rax, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+176], rax
	mov rax, r13
	sbb rax, 0
	cmovae r8, QWORD PTR [rdi+144]
	cmovae r9, QWORD PTR [rdi+152]
	cmovae r10, QWORD PTR [rdi+160]
	cmovae r11, QWORD PTR [rdi+168]
	cmovae r12, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+824], r8
	mov QWORD PTR [rdi+832], r9
	mov QWORD PTR [rdi+840], r10
	mov QWORD PTR [rdi+848], r11
	mov QWORD PTR [rdi+856], r12
	ret
	.p2align 6
