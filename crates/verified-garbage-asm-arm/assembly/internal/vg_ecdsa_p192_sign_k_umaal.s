// The functions of `src/internal/vg_ecdsa_p192_sign_k_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p192_sign_k_umaal:
	ldr r12, [sp, #0]
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r8, [r12, #16]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	mov lr, r0
	ldr r4, [r3, #20]
	rev r4, r4
	str r4, [r12, #808]
	ldr r4, [r3, #16]
	rev r4, r4
	str r4, [r12, #812]
	ldr r4, [r3, #12]
	rev r4, r4
	str r4, [r12, #816]
	ldr r4, [r3, #8]
	rev r4, r4
	str r4, [r12, #820]
	ldr r4, [r3, #4]
	rev r4, r4
	str r4, [r12, #824]
	ldr r4, [r3, #0]
	rev r4, r4
	str r4, [r12, #828]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #832]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #836]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #840]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #844]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #848]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #852]
	ldr r4, [r2, #20]
	rev r4, r4
	str r4, [r12, #856]
	ldr r4, [r2, #16]
	rev r4, r4
	str r4, [r12, #860]
	ldr r4, [r2, #12]
	rev r4, r4
	str r4, [r12, #864]
	ldr r4, [r2, #8]
	rev r4, r4
	str r4, [r12, #868]
	ldr r4, [r2, #4]
	rev r4, r4
	str r4, [r12, #872]
	ldr r4, [r2, #0]
	rev r4, r4
	str r4, [r12, #876]
	movw r10, #:lower16:({VG_P192_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P192_FRAME_CONSTS}
2:
	add r10, pc
3:
	mov r11, #51
20:
	sub r11, r11, #1
	add r5, r10, r11, lsl #3
	ldr r4, [r5, #0]
	ldr r5, [r5, #4]
	add r9, r12, r11, lsl #3
	str r4, [r9, #64]
	str r5, [r9, #68]
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1120]
	mov r11, #24
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #808]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #0]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #1]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #2]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #3]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #4]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #5]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #6]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #7]
	cmp r11, #0
	bne 21b
	mov r11, #24
22:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #352]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #192]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #193]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #194]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #195]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #196]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #197]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #198]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #199]
	cmp r11, #0
	bne 22b
	mov r11, #24
23:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #376]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #384]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #385]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #386]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #387]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #388]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #389]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #390]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #391]
	cmp r11, #0
	bne 23b
	ldr r4, [r12, #256]
	str r4, [r12, #3576]
	ldr r4, [r12, #260]
	str r4, [r12, #3580]
	ldr r4, [r12, #264]
	str r4, [r12, #3584]
	ldr r4, [r12, #268]
	str r4, [r12, #3588]
	ldr r4, [r12, #272]
	str r4, [r12, #3592]
	ldr r4, [r12, #276]
	str r4, [r12, #3596]
	ldr r4, [r12, #280]
	str r4, [r12, #3600]
	ldr r4, [r12, #284]
	str r4, [r12, #3604]
	ldr r4, [r12, #288]
	str r4, [r12, #3608]
	ldr r4, [r12, #292]
	str r4, [r12, #3612]
	ldr r4, [r12, #296]
	str r4, [r12, #3616]
	ldr r4, [r12, #300]
	str r4, [r12, #3620]
	ldr r4, [r12, #184]
	str r4, [r12, #3624]
	ldr r4, [r12, #188]
	str r4, [r12, #3628]
	ldr r4, [r12, #192]
	str r4, [r12, #3632]
	ldr r4, [r12, #196]
	str r4, [r12, #3636]
	ldr r4, [r12, #200]
	str r4, [r12, #3640]
	ldr r4, [r12, #204]
	str r4, [r12, #3644]
	ldr r4, [r12, #208]
	str r4, [r12, #3648]
	ldr r4, [r12, #212]
	str r4, [r12, #3652]
	ldr r4, [r12, #216]
	str r4, [r12, #3656]
	ldr r4, [r12, #220]
	str r4, [r12, #3660]
	ldr r4, [r12, #224]
	str r4, [r12, #3664]
	ldr r4, [r12, #228]
	str r4, [r12, #3668]
	ldr r4, [r12, #232]
	str r4, [r12, #3672]
	ldr r4, [r12, #236]
	str r4, [r12, #3676]
	ldr r4, [r12, #240]
	str r4, [r12, #3680]
	ldr r4, [r12, #244]
	str r4, [r12, #3684]
	ldr r4, [r12, #248]
	str r4, [r12, #3688]
	ldr r4, [r12, #252]
	str r4, [r12, #3692]
	movw r4, #56469
	movt r4, #29780
	str r4, [r12, #400]
	movw r4, #63566
	movt r4, #32077
	str r4, [r12, #404]
	movw r4, #27680
	movt r4, #12314
	str r4, [r12, #408]
	movw r4, #15411
	movt r4, #16182
	str r4, [r12, #412]
	movw r4, #13504
	movt r4, #9193
	str r4, [r12, #416]
	movw r4, #37203
	movt r4, #59300
	str r4, [r12, #420]
	movw r4, #22637
	movt r4, #42846
	str r4, [r12, #424]
	movw r4, #61792
	movt r4, #2186
	str r4, [r12, #428]
	movw r4, #55329
	movt r4, #63654
	str r4, [r12, #432]
	movw r4, #43566
	movt r4, #6456
	str r4, [r12, #436]
	movw r4, #2609
	movt r4, #58199
	str r4, [r12, #440]
	movw r4, #64130
	movt r4, #11575
	str r4, [r12, #444]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #448]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #452]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #456]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #460]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #464]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #468]
	mov r11, #28
24:
	sub r11, r11, #1
	mov r4, #7
	mul r4, r4, r11
	add r4, r12, r4
	add r4, r4, #4096
	cmp r11, #27
	beq 25f
	mov r9, #0
	add r9, r9, r9
	ldrb r5, [r4, #6]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #5]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #4]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #3]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #2]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #1]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #0]
	add r9, r9, r5
	b 26f
25:
	mov r9, #0
	add r9, r9, r9
	ldrb r5, [r4, #2]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #1]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #0]
	add r9, r9, r5
26:
	sub r9, r9, #64
	lsr r4, r9, #31
	mov r5, #0
	sub r4, r5, r4
	eor r9, r9, r4
	sub r9, r9, r4
	movw r8, #:lower16:({VG_P192_COMB}
	movt r8, #:upper16:({VG_P192_COMB}
2:
	add r8, pc
3:
	mov r4, #3072
	mul r4, r4, r11
	add r8, r8, r4
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3576]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3580]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3584]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3588]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3592]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3596]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3600]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3604]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3608]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3612]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3616]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3620]
	mov r7, #1
27:
	eor r10, r9, r7
	sub r10, r10, #1
	lsr r10, r10, #31
	mov r5, #0
	sub r10, r5, r10
	ldr r4, [r12, #3576]
	ldr r5, [r8, #0]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3576]
	ldr r4, [r12, #3580]
	ldr r5, [r8, #4]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3580]
	ldr r4, [r12, #3584]
	ldr r5, [r8, #8]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3584]
	ldr r4, [r12, #3588]
	ldr r5, [r8, #12]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3588]
	ldr r4, [r12, #3592]
	ldr r5, [r8, #16]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3592]
	ldr r4, [r12, #3596]
	ldr r5, [r8, #20]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3596]
	ldr r4, [r12, #3600]
	ldr r5, [r8, #24]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3600]
	ldr r4, [r12, #3604]
	ldr r5, [r8, #28]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3604]
	ldr r4, [r12, #3608]
	ldr r5, [r8, #32]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3608]
	ldr r4, [r12, #3612]
	ldr r5, [r8, #36]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3612]
	ldr r4, [r12, #3616]
	ldr r5, [r8, #40]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3616]
	ldr r4, [r12, #3620]
	ldr r5, [r8, #44]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3620]
	add r8, r8, #48
	add r7, r7, #1
	cmp r7, #65
	bne 27b
	movw r4, #1
	movt r4, #0
	str r4, [r12, #3624]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3628]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #3632]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3636]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3640]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3644]
	eor r10, r9, #0
	sub r10, r10, #1
	lsr r10, r10, #31
	mov r5, #0
	sub r10, r5, r10
	ldr r4, [r12, #3600]
	ldr r5, [r12, #3624]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3600]
	ldr r4, [r12, #3604]
	ldr r5, [r12, #3628]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3604]
	ldr r4, [r12, #3608]
	ldr r5, [r12, #3632]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3608]
	ldr r4, [r12, #3612]
	ldr r5, [r12, #3636]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3612]
	ldr r4, [r12, #3616]
	ldr r5, [r12, #3640]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3616]
	ldr r4, [r12, #3620]
	ldr r5, [r12, #3644]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3620]
	ldr r4, [r12, #3624]
	ldr r5, [r12, #136]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3624]
	ldr r4, [r12, #3628]
	ldr r5, [r12, #140]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3628]
	ldr r4, [r12, #3632]
	ldr r5, [r12, #144]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3632]
	ldr r4, [r12, #3636]
	ldr r5, [r12, #148]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3636]
	ldr r4, [r12, #3640]
	ldr r5, [r12, #152]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3640]
	ldr r4, [r12, #3644]
	ldr r5, [r12, #156]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3644]
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #136
	movw r3, #3600
	bl {vg_p192_sub_mod_p_umaal}
	mov lr, r10
	cmp r11, #27
	beq 28f
	mov r4, #7
	mul r4, r4, r11
	add r4, r12, r4
	add r4, r4, #4096
	ldrb r4, [r4, #6]
	sub r10, r4, #1
	b 29f
28:
	movw r10, #65535
	movt r10, #65535
29:
	ldr r4, [r12, #3600]
	ldr r5, [r12, #544]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3600]
	ldr r4, [r12, #3604]
	ldr r5, [r12, #548]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3604]
	ldr r4, [r12, #3608]
	ldr r5, [r12, #552]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3608]
	ldr r4, [r12, #3612]
	ldr r5, [r12, #556]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3612]
	ldr r4, [r12, #3616]
	ldr r5, [r12, #560]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3616]
	ldr r4, [r12, #3620]
	ldr r5, [r12, #564]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3620]
	ldr r4, [r12, #400]
	str r4, [r12, #3504]
	ldr r4, [r12, #404]
	str r4, [r12, #3508]
	ldr r4, [r12, #408]
	str r4, [r12, #3512]
	ldr r4, [r12, #412]
	str r4, [r12, #3516]
	ldr r4, [r12, #416]
	str r4, [r12, #3520]
	ldr r4, [r12, #420]
	str r4, [r12, #3524]
	ldr r4, [r12, #424]
	str r4, [r12, #3528]
	ldr r4, [r12, #428]
	str r4, [r12, #3532]
	ldr r4, [r12, #432]
	str r4, [r12, #3536]
	ldr r4, [r12, #436]
	str r4, [r12, #3540]
	ldr r4, [r12, #440]
	str r4, [r12, #3544]
	ldr r4, [r12, #444]
	str r4, [r12, #3548]
	ldr r4, [r12, #448]
	str r4, [r12, #3552]
	ldr r4, [r12, #452]
	str r4, [r12, #3556]
	ldr r4, [r12, #456]
	str r4, [r12, #3560]
	ldr r4, [r12, #460]
	str r4, [r12, #3564]
	ldr r4, [r12, #464]
	str r4, [r12, #3568]
	ldr r4, [r12, #468]
	str r4, [r12, #3572]
	mov r10, lr
	mov r0, r12
	bl {vg_p192_point_add_umaal}
	mov lr, r10
	ldr r4, [r12, #3432]
	str r4, [r12, #400]
	ldr r4, [r12, #3436]
	str r4, [r12, #404]
	ldr r4, [r12, #3440]
	str r4, [r12, #408]
	ldr r4, [r12, #3444]
	str r4, [r12, #412]
	ldr r4, [r12, #3448]
	str r4, [r12, #416]
	ldr r4, [r12, #3452]
	str r4, [r12, #420]
	ldr r4, [r12, #3456]
	str r4, [r12, #424]
	ldr r4, [r12, #3460]
	str r4, [r12, #428]
	ldr r4, [r12, #3464]
	str r4, [r12, #432]
	ldr r4, [r12, #3468]
	str r4, [r12, #436]
	ldr r4, [r12, #3472]
	str r4, [r12, #440]
	ldr r4, [r12, #3476]
	str r4, [r12, #444]
	ldr r4, [r12, #3480]
	str r4, [r12, #448]
	ldr r4, [r12, #3484]
	str r4, [r12, #452]
	ldr r4, [r12, #3488]
	str r4, [r12, #456]
	ldr r4, [r12, #3492]
	str r4, [r12, #460]
	ldr r4, [r12, #3496]
	str r4, [r12, #464]
	ldr r4, [r12, #3500]
	str r4, [r12, #468]
	cmp r11, #0
	bne 24b
	ldr r4, [r12, #184]
	str r4, [r12, #760]
	ldr r4, [r12, #188]
	str r4, [r12, #764]
	ldr r4, [r12, #192]
	str r4, [r12, #768]
	ldr r4, [r12, #196]
	str r4, [r12, #772]
	ldr r4, [r12, #200]
	str r4, [r12, #776]
	ldr r4, [r12, #204]
	str r4, [r12, #780]
	mov r11, #192
210:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #760
	movw r2, #760
	movw r3, #760
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #760
	movw r3, #448
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #192]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #760]
	ldr r5, [r12, #784]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #760]
	ldr r4, [r12, #764]
	ldr r5, [r12, #788]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #764]
	ldr r4, [r12, #768]
	ldr r5, [r12, #792]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #768]
	ldr r4, [r12, #772]
	ldr r5, [r12, #796]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #772]
	ldr r4, [r12, #776]
	ldr r5, [r12, #800]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #776]
	ldr r4, [r12, #780]
	ldr r5, [r12, #804]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #780]
	cmp r11, #0
	bne 210b
	mov r10, lr
	mov r0, r12
	movw r1, #880
	movw r2, #400
	movw r3, #760
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #880
	movw r3, #160
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #904
	movw r3, #136
	bl {vg_p192_add_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #952
	movw r2, #808
	movw r3, #304
	bl {vg_p192_mul_mod_n_umaal}
	mov lr, r10
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #832]
	ldr r8, [r12, #88]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #836]
	ldr r8, [r12, #92]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #840]
	ldr r8, [r12, #96]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #844]
	ldr r8, [r12, #100]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #848]
	ldr r8, [r12, #104]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #852]
	ldr r8, [r12, #108]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	sub r5, r3, #1
	mov r9, r5
	ldr r5, [r12, #832]
	ldr r4, [r12, #836]
	orr r5, r5, r4
	ldr r4, [r12, #840]
	orr r5, r5, r4
	ldr r4, [r12, #844]
	orr r5, r5, r4
	ldr r4, [r12, #848]
	orr r5, r5, r4
	ldr r4, [r12, #852]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	and r5, r5, r9
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #808]
	ldr r8, [r12, #88]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #812]
	ldr r8, [r12, #92]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #816]
	ldr r8, [r12, #96]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #820]
	ldr r8, [r12, #100]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #824]
	ldr r8, [r12, #104]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #828]
	ldr r8, [r12, #108]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	sub r5, r3, #1
	mov r9, r5
	ldr r5, [r12, #808]
	ldr r4, [r12, #812]
	orr r5, r5, r4
	ldr r4, [r12, #816]
	orr r5, r5, r4
	ldr r4, [r12, #820]
	orr r5, r5, r4
	ldr r4, [r12, #824]
	orr r5, r5, r4
	ldr r4, [r12, #828]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	and r5, r5, r9
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	ldr r5, [r12, #928]
	ldr r4, [r12, #932]
	orr r5, r5, r4
	ldr r4, [r12, #936]
	orr r5, r5, r4
	ldr r4, [r12, #940]
	orr r5, r5, r4
	ldr r4, [r12, #944]
	orr r5, r5, r4
	ldr r4, [r12, #948]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	ldr r4, [r12, #328]
	str r4, [r12, #760]
	ldr r4, [r12, #332]
	str r4, [r12, #764]
	ldr r4, [r12, #336]
	str r4, [r12, #768]
	ldr r4, [r12, #340]
	str r4, [r12, #772]
	ldr r4, [r12, #344]
	str r4, [r12, #776]
	ldr r4, [r12, #348]
	str r4, [r12, #780]
	mov r11, #192
211:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #760
	movw r2, #760
	movw r3, #760
	bl {vg_p192_mul_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #760
	movw r3, #952
	bl {vg_p192_mul_mod_n_umaal}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #384]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #760]
	ldr r5, [r12, #784]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #760]
	ldr r4, [r12, #764]
	ldr r5, [r12, #788]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #764]
	ldr r4, [r12, #768]
	ldr r5, [r12, #792]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #768]
	ldr r4, [r12, #772]
	ldr r5, [r12, #796]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #772]
	ldr r4, [r12, #776]
	ldr r5, [r12, #800]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #776]
	ldr r4, [r12, #780]
	ldr r5, [r12, #804]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #780]
	cmp r11, #0
	bne 211b
	mov r10, lr
	mov r0, r12
	movw r1, #976
	movw r2, #928
	movw r3, #304
	bl {vg_p192_mul_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1000
	movw r2, #832
	movw r3, #304
	bl {vg_p192_mul_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #856
	movw r3, #304
	bl {vg_p192_mul_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #976
	movw r3, #1000
	bl {vg_p192_mul_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #1048
	movw r3, #1024
	bl {vg_p192_add_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1072
	movw r2, #760
	movw r3, #1048
	bl {vg_p192_mul_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1096
	movw r2, #1072
	movw r3, #160
	bl {vg_p192_mul_mod_n_umaal}
	mov lr, r10
	ldr r5, [r12, #1096]
	ldr r4, [r12, #1100]
	orr r5, r5, r4
	ldr r4, [r12, #1104]
	orr r5, r5, r4
	ldr r4, [r12, #1108]
	orr r5, r5, r4
	ldr r4, [r12, #1112]
	orr r5, r5, r4
	ldr r4, [r12, #1116]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	ldr r10, [r12, #1120]
	ldr r4, [r12, #928]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #20]
	ldr r4, [r12, #932]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #16]
	ldr r4, [r12, #936]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #12]
	ldr r4, [r12, #940]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #8]
	ldr r4, [r12, #944]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #4]
	ldr r4, [r12, #948]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #0]
	ldr r4, [r12, #1096]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #44]
	ldr r4, [r12, #1100]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #40]
	ldr r4, [r12, #1104]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #36]
	ldr r4, [r12, #1108]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #32]
	ldr r4, [r12, #1112]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #28]
	ldr r4, [r12, #1116]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #24]
	and r0, r10, #1
	ldr r4, [r12, #0]
	ldr r5, [r12, #4]
	ldr r6, [r12, #8]
	ldr r7, [r12, #12]
	ldr r8, [r12, #16]
	ldr r9, [r12, #20]
	ldr r10, [r12, #24]
	ldr r11, [r12, #28]
	ldr lr, [r12, #32]
	bx lr
