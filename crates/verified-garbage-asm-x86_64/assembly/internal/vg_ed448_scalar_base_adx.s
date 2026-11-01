// The functions of `src/internal/vg_ed448_scalar_base_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_scalar_base_adx:
	mov QWORD PTR [rdx], rbx
	mov QWORD PTR [rdx+8], rbp
	mov QWORD PTR [rdx+16], r12
	mov QWORD PTR [rdx+24], r13
	mov QWORD PTR [rdx+32], r14
	mov QWORD PTR [rdx+40], r15
	mov r15, rdi
	mov rdi, rdx
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	movabs r8, 2749069528532828254
	movabs r9, 4844607530355168142
	movabs r10, 1346042987506197777
	movabs r11, -1554336549866068892
	movabs r12, -7055903183279810713
	movabs r13, 2458144774905870042
	movabs r14, 5699710800930606573
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	movabs r8, -7491604544318539244
	movabs r9, -162952930493216595
	movabs r10, 4239012173876836804
	movabs r11, -8685020228626627881
	movabs r12, 5470311636975982656
	movabs r13, -8613661815248140446
	movabs r14, 7583857750517922852
	mov QWORD PTR [rdi+640], r8
	mov QWORD PTR [rdi+648], r9
	mov QWORD PTR [rdi+656], r10
	mov QWORD PTR [rdi+664], r11
	mov QWORD PTR [rdi+672], r12
	mov QWORD PTR [rdi+680], r13
	mov QWORD PTR [rdi+688], r14
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+704], r8
	mov QWORD PTR [rdi+712], r9
	mov QWORD PTR [rdi+720], r10
	mov QWORD PTR [rdi+728], r11
	mov QWORD PTR [rdi+736], r12
	mov QWORD PTR [rdi+744], r13
	mov QWORD PTR [rdi+752], r14
	movabs r8, -39082
	movabs r9, -1
	movabs r10, -1
	movabs r11, -4294967297
	movabs r12, -1
	movabs r13, -1
	movabs r14, -1
	mov QWORD PTR [rdi+768], r8
	mov QWORD PTR [rdi+776], r9
	mov QWORD PTR [rdi+784], r10
	mov QWORD PTR [rdi+792], r11
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rsi+rbx*1]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2048], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2049], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2050], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2051], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2052], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2053], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2054], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2055], dl
	add rbx, 1
	cmp rbx, 57
	jne 20b
	mov QWORD PTR [rdi+48], r15
	mov rsi, r15
	mov ebx, 114
21:
	sub rbx, 1
	call {vg_ed448_r64_point_double_adx}
	movabs r8, 0
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	movabs r12, 0
	movabs r13, 0
	movabs r14, 0
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 0
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, 2749069528532828254
	movabs r9, 4844607530355168142
	movabs r10, 1346042987506197777
	movabs r11, -1554336549866068892
	movabs r12, -7055903183279810713
	movabs r13, 2458144774905870042
	movabs r14, 5699710800930606573
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, -7491604544318539244
	movabs r9, -162952930493216595
	movabs r10, 4239012173876836804
	movabs r11, -8685020228626627881
	movabs r12, 5470311636975982656
	movabs r13, -8613661815248140446
	movabs r14, 7583857750517922852
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 1
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, 8476786567168877144
	movabs r9, -2314234268006181703
	movabs r10, 4900457673962889283
	movabs r11, -4834407711458556773
	movabs r12, -3138605425432715589
	movabs r13, 1816374484619006845
	movabs r14, 2742009522714786716
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, -5251902906361450077
	movabs r9, -1346548124728273842
	movabs r10, -6868364787628893876
	movabs r11, -2130981827691279384
	movabs r12, 8550329732868618762
	movabs r13, 4861322587364674033
	movabs r14, -5563315882851820428
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 2
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, -6883104612690751721
	movabs r9, 1302957142708968366
	movabs r10, -2374259868669405312
	movabs r11, -2087150705783029941
	movabs r12, 9206582763775039926
	movabs r13, 4442466098178225627
	movabs r14, -3519033093842493678
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, 2850704633646404851
	movabs r9, -7691203833508733001
	movabs r10, -6156258291514430863
	movabs r11, -3503443754931576384
	movabs r12, -3941084127381473226
	movabs r13, -5014355107601480022
	movabs r14, 3030966416740923162
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 3
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, 5473959769461929568
	movabs r9, 1160653111361746410
	movabs r10, -7835412994044195166
	movabs r11, -3673184946560233423
	movabs r12, 843686057780763752
	movabs r13, 6938642973991502469
	movabs r14, 304388332870265350
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, -6925556042019212651
	movabs r9, 8079562902487926234
	movabs r10, -6761850020911227168
	movabs r11, -1637402680460057473
	movabs r12, 3852271263334335143
	movabs r13, 2319491162962954939
	movabs r14, -1726771370465284483
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 4
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, 2481400398930568261
	movabs r9, -6743137452074519768
	movabs r10, -5015702305884632307
	movabs r11, 4177468630837878711
	movabs r12, 8184176015566594014
	movabs r13, -8131818316798540591
	movabs r14, 1813655758263815040
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, -8714590863143903621
	movabs r9, -3672856716973811893
	movabs r10, -1698797131649473986
	movabs r11, 7976223299843096485
	movabs r12, 7637643269915391633
	movabs r13, 7640396604781089643
	movabs r14, 2708878663985405737
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 5
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, -3475845446275876726
	movabs r9, 1719908932397632593
	movabs r10, -7802449085406334199
	movabs r11, 2763083905751925048
	movabs r12, 8768446642892501011
	movabs r13, 556142426436735170
	movabs r14, 5571840851599297074
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, -5581061496372636541
	movabs r9, -3367927390856732819
	movabs r10, -4917572798429279622
	movabs r11, 59613725927233167
	movabs r12, 902735705502244361
	movabs r13, -6085969048521690241
	movabs r14, 2671330284601499796
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 6
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, -2022533952042583150
	movabs r9, -7415886146418374712
	movabs r10, -4475849828347113597
	movabs r11, 2840926305292148793
	movabs r12, 5646615169314045051
	movabs r13, -7214145702694117195
	movabs r14, 5421381891167786205
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, -1042596189054335276
	movabs r9, -9129336190292022469
	movabs r10, 7758807905550851022
	movabs r11, -5339723757402269834
	movabs r12, 5102887440008414109
	movabs r13, 6594519608203872233
	movabs r14, -7144179260832411104
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 7
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, 6408086288777134272
	movabs r9, -7874953203424683120
	movabs r10, -5598008657128468283
	movabs r11, 4267969709021920606
	movabs r12, -884332472252606074
	movabs r13, 6749163961302558518
	movabs r14, -8405588640273007556
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, -3850811272321271981
	movabs r9, -1697780216792967295
	movabs r10, 7172940744806932768
	movabs r11, 8695039594045797391
	movabs r12, -5952764174520046699
	movabs r13, 8761818474228299673
	movabs r14, 2459886060397807820
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 8
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, -3006028961793724648
	movabs r9, 7100195325546677469
	movabs r10, -1039927944951049356
	movabs r11, -8287660293266937522
	movabs r12, 893178540746101322
	movabs r13, 7792751824047469980
	movabs r14, 5169839397035113271
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, -772559868293284928
	movabs r9, 4978823913325519432
	movabs r10, 8444868394312981492
	movabs r11, 3750321246721863135
	movabs r12, 5119824999478117958
	movabs r13, 5983425823960246423
	movabs r14, 5283994718483983061
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 9
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, -427009011496462576
	movabs r9, -176083608346856260
	movabs r10, -6532879775815621354
	movabs r11, 1792030209621025489
	movabs r12, 985516991101375153
	movabs r13, -9026943860966086173
	movabs r14, 7919629121564358099
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, -6632196601877855653
	movabs r9, 8165547200347965869
	movabs r10, -5945200797176538636
	movabs r11, 4375502544888930216
	movabs r12, -6683892198370873813
	movabs r13, -8517721501772011651
	movabs r14, -2853734778493185571
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 10
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, -9145317026340900391
	movabs r9, -8579007235526122950
	movabs r10, -3966189613074341105
	movabs r11, 449959165644105103
	movabs r12, 2419287169597322850
	movabs r13, 485270871873138948
	movabs r14, 4072121982413302749
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, -1348892654287038719
	movabs r9, -7667191665289877838
	movabs r10, -6805112492164246407
	movabs r11, 6350807447189560770
	movabs r12, -7287284233306294828
	movabs r13, -7177925300378278660
	movabs r14, -1477018954814986629
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 11
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, -397377243902735754
	movabs r9, 3106836320746297630
	movabs r10, -7523028428132892550
	movabs r11, -155219412448040697
	movabs r12, -829511053260761249
	movabs r13, 256113999559477274
	movabs r14, 821118533019946359
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, 6291080852900986209
	movabs r9, 7782647537704799514
	movabs r10, -2154413580351857172
	movabs r11, -762553163870202230
	movabs r12, 7758857205949897042
	movabs r13, 7192497824938309673
	movabs r14, -4953348833181351759
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 12
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, -6341154224092063015
	movabs r9, -7554849561758496052
	movabs r10, 5011689964934432892
	movabs r11, 4379796149454460743
	movabs r12, 4854221743547531633
	movabs r13, -4168288762058693953
	movabs r14, -261114278587201555
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, -4220092344499213572
	movabs r9, -7559614831638389491
	movabs r10, 5178229751948271818
	movabs r11, -120121189533848566
	movabs r12, -1175269896242805429
	movabs r13, 2522703743598888287
	movabs r14, 4251314926296813419
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 13
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, 6532706108792931455
	movabs r9, -2125511502109289278
	movabs r10, 2092091067016684646
	movabs r11, -6208552362939238204
	movabs r12, -6335271337363820232
	movabs r13, -1181713874509189342
	movabs r14, -2381854401707592156
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, 8300271263465807730
	movabs r9, -5216178954035038225
	movabs r10, -5488397119723558483
	movabs r11, 5953346180193106969
	movabs r12, -1333753955514731723
	movabs r13, 3090552537384560716
	movabs r14, 6321505630760784403
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 14
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	movabs r8, -8158609265006769338
	movabs r9, 6348633278856198671
	movabs r10, 2428715454416313253
	movabs r11, -5789878678028916544
	movabs r12, -1121212554818974556
	movabs r13, -7055869052615924064
	movabs r14, 7971057690321048563
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	movabs r8, -3781594264426438654
	movabs r9, 6564746654706990636
	movabs r10, 6518069159384036439
	movabs r11, 679453530129020285
	movabs r12, -6977889989967989928
	movabs r13, 3456626137961454923
	movabs r14, -5925056567873128495
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	movzx eax, BYTE PTR [rdi+rbx*1+2390]
	movzx edx, BYTE PTR [rdi+rbx*1+2276]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2162]
	add rax, rax
	add rax, rdx
	movzx edx, BYTE PTR [rdi+rbx*1+2048]
	add rax, rax
	add rax, rdx
	xor rax, 15
	cmp rax, 1
	mov ecx, 0
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+576]
	mov rdx, QWORD PTR [rdi+256]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+576], rax
	mov QWORD PTR [rdi+256], rdx
	mov rax, QWORD PTR [rdi+584]
	mov rdx, QWORD PTR [rdi+264]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+584], rax
	mov QWORD PTR [rdi+264], rdx
	mov rax, QWORD PTR [rdi+592]
	mov rdx, QWORD PTR [rdi+272]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+592], rax
	mov QWORD PTR [rdi+272], rdx
	mov rax, QWORD PTR [rdi+600]
	mov rdx, QWORD PTR [rdi+280]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+600], rax
	mov QWORD PTR [rdi+280], rdx
	mov rax, QWORD PTR [rdi+608]
	mov rdx, QWORD PTR [rdi+288]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+608], rax
	mov QWORD PTR [rdi+288], rdx
	mov rax, QWORD PTR [rdi+616]
	mov rdx, QWORD PTR [rdi+296]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+616], rax
	mov QWORD PTR [rdi+296], rdx
	mov rax, QWORD PTR [rdi+624]
	mov rdx, QWORD PTR [rdi+304]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+624], rax
	mov QWORD PTR [rdi+304], rdx
	mov rax, QWORD PTR [rdi+640]
	mov rdx, QWORD PTR [rdi+320]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+640], rax
	mov QWORD PTR [rdi+320], rdx
	mov rax, QWORD PTR [rdi+648]
	mov rdx, QWORD PTR [rdi+328]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+648], rax
	mov QWORD PTR [rdi+328], rdx
	mov rax, QWORD PTR [rdi+656]
	mov rdx, QWORD PTR [rdi+336]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+656], rax
	mov QWORD PTR [rdi+336], rdx
	mov rax, QWORD PTR [rdi+664]
	mov rdx, QWORD PTR [rdi+344]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+664], rax
	mov QWORD PTR [rdi+344], rdx
	mov rax, QWORD PTR [rdi+672]
	mov rdx, QWORD PTR [rdi+352]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+672], rax
	mov QWORD PTR [rdi+352], rdx
	mov rax, QWORD PTR [rdi+680]
	mov rdx, QWORD PTR [rdi+360]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+680], rax
	mov QWORD PTR [rdi+360], rdx
	mov rax, QWORD PTR [rdi+688]
	mov rdx, QWORD PTR [rdi+368]
	mov r8, rax
	xor r8, rdx
	and r8, rcx
	xor rax, r8
	xor rdx, r8
	mov QWORD PTR [rdi+688], rax
	mov QWORD PTR [rdi+368], rdx
	call {vg_ed448_r64_point_add_affine_adx}
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov QWORD PTR [rdi+96], r12
	mov QWORD PTR [rdi+104], r13
	mov QWORD PTR [rdi+112], r14
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov r8, QWORD PTR [rdi+384]
	mov r9, QWORD PTR [rdi+392]
	mov r10, QWORD PTR [rdi+400]
	mov r11, QWORD PTR [rdi+408]
	mov r12, QWORD PTR [rdi+416]
	mov r13, QWORD PTR [rdi+424]
	mov r14, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	test rbx, rbx
	jne 21b
	mov QWORD PTR [rdi+48], rsi
	mov r8, QWORD PTR [rdi+192]
	mov r9, QWORD PTR [rdi+200]
	mov r10, QWORD PTR [rdi+208]
	mov r11, QWORD PTR [rdi+216]
	mov r12, QWORD PTR [rdi+224]
	mov r13, QWORD PTR [rdi+232]
	mov r14, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov r12, QWORD PTR [rdi+48]
	call {vg_gf448_r64_pow223_adx}
	mov QWORD PTR [rdi+48], r12
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov QWORD PTR [rdi+1536], r9
	mov QWORD PTR [rdi+1640], r9
	mov rdx, QWORD PTR [rdi+1408]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1416]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1544], r9
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1416]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1560], r11
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1424]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1576], r13
	mov QWORD PTR [rdi+1584], r14
	mov rdx, QWORD PTR [rdi+1432]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov rdx, QWORD PTR [rdi+1440]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov rdx, QWORD PTR [rdi+1448]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1408]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1536]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1544]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1536], r8
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1416]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1552]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1560]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1552], r8
	mov QWORD PTR [rdi+1560], r9
	mov rdx, QWORD PTR [rdi+1424]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1568]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1576]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1568], r8
	mov QWORD PTR [rdi+1576], r9
	mov rdx, QWORD PTR [rdi+1432]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1584]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1592]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1584], r8
	mov QWORD PTR [rdi+1592], r9
	mov rdx, QWORD PTR [rdi+1440]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1600]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1608]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov rdx, QWORD PTR [rdi+1448]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1616]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1624]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1616], r8
	mov QWORD PTR [rdi+1624], r9
	mov rdx, QWORD PTR [rdi+1456]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1632]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1640]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1632], r8
	mov QWORD PTR [rdi+1640], r9
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov QWORD PTR [rdi+1456], r14
	mov ebx, 224
22:
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov QWORD PTR [rdi+1536], r9
	mov QWORD PTR [rdi+1640], r9
	mov rdx, QWORD PTR [rdi+1408]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1416]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1544], r9
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1416]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1560], r11
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1424]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1576], r13
	mov QWORD PTR [rdi+1584], r14
	mov rdx, QWORD PTR [rdi+1432]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov rdx, QWORD PTR [rdi+1440]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov rdx, QWORD PTR [rdi+1448]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1408]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1536]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1544]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1536], r8
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1416]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1552]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1560]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1552], r8
	mov QWORD PTR [rdi+1560], r9
	mov rdx, QWORD PTR [rdi+1424]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1568]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1576]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1568], r8
	mov QWORD PTR [rdi+1576], r9
	mov rdx, QWORD PTR [rdi+1432]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1584]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1592]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1584], r8
	mov QWORD PTR [rdi+1592], r9
	mov rdx, QWORD PTR [rdi+1440]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1600]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1608]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov rdx, QWORD PTR [rdi+1448]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1616]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1624]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1616], r8
	mov QWORD PTR [rdi+1624], r9
	mov rdx, QWORD PTR [rdi+1456]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1632]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1640]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1632], r8
	mov QWORD PTR [rdi+1640], r9
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov QWORD PTR [rdi+1456], r14
	sub rbx, 1
	jne 22b
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov QWORD PTR [rdi+1536], r9
	mov QWORD PTR [rdi+1640], r9
	mov rdx, QWORD PTR [rdi+1344]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1544], r9
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1352]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1560], r11
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1360]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1576], r13
	mov QWORD PTR [rdi+1584], r14
	mov rdx, QWORD PTR [rdi+1368]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov rdx, QWORD PTR [rdi+1376]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov rdx, QWORD PTR [rdi+1384]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1344]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1536]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1544]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1536], r8
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1352]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1552]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1560]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1552], r8
	mov QWORD PTR [rdi+1560], r9
	mov rdx, QWORD PTR [rdi+1360]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1568]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1576]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1568], r8
	mov QWORD PTR [rdi+1576], r9
	mov rdx, QWORD PTR [rdi+1368]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1584]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1592]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1584], r8
	mov QWORD PTR [rdi+1592], r9
	mov rdx, QWORD PTR [rdi+1376]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1600]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1608]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov rdx, QWORD PTR [rdi+1384]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1616]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1624]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1616], r8
	mov QWORD PTR [rdi+1624], r9
	mov rdx, QWORD PTR [rdi+1392]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1632]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1640]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1632], r8
	mov QWORD PTR [rdi+1640], r9
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1344], r8
	mov QWORD PTR [rdi+1352], r9
	mov QWORD PTR [rdi+1360], r10
	mov QWORD PTR [rdi+1368], r11
	mov QWORD PTR [rdi+1376], r12
	mov QWORD PTR [rdi+1384], r13
	mov QWORD PTR [rdi+1392], r14
	mov ebx, 1
23:
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov QWORD PTR [rdi+1536], r9
	mov QWORD PTR [rdi+1640], r9
	mov rdx, QWORD PTR [rdi+1344]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1544], r9
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1352]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1560], r11
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1360]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1576], r13
	mov QWORD PTR [rdi+1584], r14
	mov rdx, QWORD PTR [rdi+1368]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov rdx, QWORD PTR [rdi+1376]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov rdx, QWORD PTR [rdi+1384]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1344]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1536]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1544]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1536], r8
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1352]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1552]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1560]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1552], r8
	mov QWORD PTR [rdi+1560], r9
	mov rdx, QWORD PTR [rdi+1360]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1568]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1576]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1568], r8
	mov QWORD PTR [rdi+1576], r9
	mov rdx, QWORD PTR [rdi+1368]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1584]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1592]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1584], r8
	mov QWORD PTR [rdi+1592], r9
	mov rdx, QWORD PTR [rdi+1376]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1600]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1608]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov rdx, QWORD PTR [rdi+1384]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1616]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1624]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1616], r8
	mov QWORD PTR [rdi+1624], r9
	mov rdx, QWORD PTR [rdi+1392]
	mulx rcx, rax, rdx
	mov r8, QWORD PTR [rdi+1632]
	adcx r8, r8
	adox r8, rax
	mov r9, QWORD PTR [rdi+1640]
	adcx r9, r9
	adox r9, rcx
	mov QWORD PTR [rdi+1632], r8
	mov QWORD PTR [rdi+1640], r9
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1344], r8
	mov QWORD PTR [rdi+1352], r9
	mov QWORD PTR [rdi+1360], r10
	mov QWORD PTR [rdi+1368], r11
	mov QWORD PTR [rdi+1376], r12
	mov QWORD PTR [rdi+1384], r13
	mov QWORD PTR [rdi+1392], r14
	sub rbx, 1
	jne 23b
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+192]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+200]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+208]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+216]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+224]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+232]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+240]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	mov QWORD PTR [rdi+1584], r14
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	mov QWORD PTR [rdi+1640], r13
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1344], r8
	mov QWORD PTR [rdi+1352], r9
	mov QWORD PTR [rdi+1360], r10
	mov QWORD PTR [rdi+1368], r11
	mov QWORD PTR [rdi+1376], r12
	mov QWORD PTR [rdi+1384], r13
	mov QWORD PTR [rdi+1392], r14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+1344]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1408]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1416]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+1352]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1408]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1416]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1360]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1408]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1416]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1368]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1408]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1416]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+1376]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1408]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1416]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1384]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1408]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1416]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+1392]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1408]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1416]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	mov QWORD PTR [rdi+1584], r14
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	mov QWORD PTR [rdi+1640], r13
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	mov QWORD PTR [rdi+1440], r12
	mov QWORD PTR [rdi+1448], r13
	mov QWORD PTR [rdi+1456], r14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+1408]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+88]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+1416]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+88]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1424]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+88]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1432]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+88]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+1440]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+88]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1448]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+88]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+1456]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+88]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	mov QWORD PTR [rdi+1584], r14
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	mov QWORD PTR [rdi+1640], r13
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	mov QWORD PTR [rdi+288], r12
	mov QWORD PTR [rdi+296], r13
	mov QWORD PTR [rdi+304], r14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+1408]
	mov r15d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+128]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	mov QWORD PTR [rdi+1536], r8
	mov rdx, QWORD PTR [rdi+1416]
	mov r8d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+128]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	mov QWORD PTR [rdi+1544], r9
	mov rdx, QWORD PTR [rdi+1424]
	mov r9d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+128]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	mov QWORD PTR [rdi+1552], r10
	mov rdx, QWORD PTR [rdi+1432]
	mov r10d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+128]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	mov QWORD PTR [rdi+1560], r11
	mov rdx, QWORD PTR [rdi+1440]
	mov r11d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+128]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	mov QWORD PTR [rdi+1568], r12
	mov rdx, QWORD PTR [rdi+1448]
	mov r12d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+128]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r11, rax
	adcx r12, rcx
	adox r12, rbp
	mov QWORD PTR [rdi+1576], r13
	mov rdx, QWORD PTR [rdi+1456]
	mov r13d, 0
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+128]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+136]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+144]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+152]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+160]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+168]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+176]
	adox r12, rax
	adcx r13, rcx
	adox r13, rbp
	mov QWORD PTR [rdi+1584], r14
	mov QWORD PTR [rdi+1592], r15
	mov QWORD PTR [rdi+1600], r8
	mov QWORD PTR [rdi+1608], r9
	mov QWORD PTR [rdi+1616], r10
	mov QWORD PTR [rdi+1624], r11
	mov QWORD PTR [rdi+1632], r12
	mov QWORD PTR [rdi+1640], r13
	mov r15d, 0
	mov r8, QWORD PTR [rdi+1536]
	mov r9, QWORD PTR [rdi+1544]
	mov r10, QWORD PTR [rdi+1552]
	mov r11, QWORD PTR [rdi+1560]
	mov r12, QWORD PTR [rdi+1568]
	mov r13, QWORD PTR [rdi+1576]
	mov r14, QWORD PTR [rdi+1584]
	add r8, QWORD PTR [rdi+1592]
	adc r9, QWORD PTR [rdi+1600]
	adc r10, QWORD PTR [rdi+1608]
	adc r11, QWORD PTR [rdi+1616]
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rax, QWORD PTR [rdi+1616]
	mov edx, eax
	sub rax, rdx
	add r11, rax
	adc r12, QWORD PTR [rdi+1624]
	adc r13, QWORD PTR [rdi+1632]
	adc r14, QWORD PTR [rdi+1640]
	adc r15, 0
	mov rcx, QWORD PTR [rdi+1588]
	mov edx, ecx
	sub rcx, rdx
	mov edx, DWORD PTR [rdi+1644]
	add rcx, rdx
	add r8, QWORD PTR [rdi+1620]
	adc r9, QWORD PTR [rdi+1628]
	adc r10, QWORD PTR [rdi+1636]
	adc r11, rcx
	adc r12, QWORD PTR [rdi+1596]
	adc r13, QWORD PTR [rdi+1604]
	adc r14, QWORD PTR [rdi+1612]
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov r15d, 0
	adc r15, 0
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+320], r8
	mov QWORD PTR [rdi+328], r9
	mov QWORD PTR [rdi+336], r10
	mov QWORD PTR [rdi+344], r11
	mov QWORD PTR [rdi+352], r12
	mov QWORD PTR [rdi+360], r13
	mov QWORD PTR [rdi+368], r14
	mov r15d, 1
	mov r8, QWORD PTR [rdi+256]
	mov r9, QWORD PTR [rdi+264]
	mov r10, QWORD PTR [rdi+272]
	mov r11, QWORD PTR [rdi+280]
	mov r12, QWORD PTR [rdi+288]
	mov r13, QWORD PTR [rdi+296]
	mov r14, QWORD PTR [rdi+304]
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	sbb r15, r15
	mov rax, QWORD PTR [rdi+256]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+264]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+272]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+280]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+288]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+296]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+304]
	xor r14, rax
	and r14, r15
	xor r14, rax
	mov rsi, r8
	and rsi, 1
	ror rsi, 57
	mov r15d, 1
	mov r8, QWORD PTR [rdi+320]
	mov r9, QWORD PTR [rdi+328]
	mov r10, QWORD PTR [rdi+336]
	mov r11, QWORD PTR [rdi+344]
	mov r12, QWORD PTR [rdi+352]
	mov r13, QWORD PTR [rdi+360]
	mov r14, QWORD PTR [rdi+368]
	mov rax, r15
	ror rax, 32
	add r8, r15
	adc r9, 0
	adc r10, 0
	adc r11, rax
	adc r12, 0
	adc r13, 0
	adc r14, 0
	sbb r15, r15
	mov rax, QWORD PTR [rdi+320]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+328]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+336]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+344]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+352]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+360]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+368]
	xor r14, rax
	and r14, r15
	xor r14, rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rax], r8
	mov QWORD PTR [rax+8], r9
	mov QWORD PTR [rax+16], r10
	mov QWORD PTR [rax+24], r11
	mov QWORD PTR [rax+32], r12
	mov QWORD PTR [rax+40], r13
	mov QWORD PTR [rax+48], r14
	mov BYTE PTR [rax+56], sil
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6
