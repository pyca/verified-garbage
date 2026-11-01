// The functions of `src/camellia.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_expand_key:
	sub sp, sp, #2720
	add r3, sp, #0
	str r4, [r3, #2472]
	str r5, [r3, #2476]
	str r6, [r3, #2480]
	str r7, [r3, #2484]
	str r8, [r3, #2488]
	str r9, [r3, #2492]
	str r10, [r3, #2496]
	str r11, [r3, #2500]
	str lr, [r3, #2504]
	mov r8, r3
	str r2, [r8, #2508]
	str r1, [r8, #2512]
	movw r10, #0
	movt r10, #65280
	str r10, [r8, #288]
	movw r10, #65280
	movt r10, #65535
	str r10, [r8, #292]
	movw r10, #65280
	movt r10, #65535
	str r10, [r8, #296]
	movw r10, #65280
	movt r10, #65280
	str r10, [r8, #300]
	movw r10, #65280
	movt r10, #65280
	str r10, [r8, #304]
	movw r10, #255
	movt r10, #65535
	str r10, [r8, #308]
	movw r10, #0
	movt r10, #65535
	str r10, [r8, #312]
	movw r10, #65535
	movt r10, #0
	str r10, [r8, #316]
	movw r10, #255
	movt r10, #65280
	str r10, [r8, #320]
	movw r10, #255
	movt r10, #65280
	str r10, [r8, #324]
	movw r10, #65280
	movt r10, #0
	str r10, [r8, #328]
	movw r10, #65535
	movt r10, #65280
	str r10, [r8, #332]
	movw r10, #255
	movt r10, #255
	str r10, [r8, #336]
	movw r10, #255
	movt r10, #0
	str r10, [r8, #340]
	movw r10, #65280
	movt r10, #0
	str r10, [r8, #344]
	movw r10, #65280
	movt r10, #65535
	str r10, [r8, #348]
	movw r10, #0
	movt r10, #0
	str r10, [r8, #352]
	movw r10, #65535
	movt r10, #0
	str r10, [r8, #356]
	movw r10, #255
	movt r10, #0
	str r10, [r8, #360]
	movw r10, #65280
	movt r10, #65535
	str r10, [r8, #364]
	movw r10, #65535
	movt r10, #65280
	str r10, [r8, #368]
	movw r10, #65535
	movt r10, #255
	str r10, [r8, #372]
	movw r10, #65280
	movt r10, #65535
	str r10, [r8, #376]
	movw r10, #255
	movt r10, #255
	str r10, [r8, #380]
	movw r10, #0
	movt r10, #255
	str r10, [r8, #384]
	movw r10, #65280
	movt r10, #65535
	str r10, [r8, #388]
	movw r10, #255
	movt r10, #0
	str r10, [r8, #392]
	movw r10, #65535
	movt r10, #0
	str r10, [r8, #396]
	movw r10, #0
	movt r10, #65535
	str r10, [r8, #400]
	movw r10, #65280
	movt r10, #65535
	str r10, [r8, #404]
	movw r10, #255
	movt r10, #255
	str r10, [r8, #408]
	movw r10, #65280
	movt r10, #65280
	str r10, [r8, #412]
	movw r10, #65280
	movt r10, #65535
	str r10, [r8, #416]
	movw r10, #65535
	movt r10, #65535
	str r10, [r8, #420]
	movw r10, #65535
	movt r10, #65535
	str r10, [r8, #424]
	movw r10, #65280
	movt r10, #65280
	str r10, [r8, #428]
	movw r10, #0
	movt r10, #255
	str r10, [r8, #432]
	movw r10, #65280
	movt r10, #65535
	str r10, [r8, #436]
	movw r10, #65535
	movt r10, #0
	str r10, [r8, #440]
	movw r10, #65535
	movt r10, #0
	str r10, [r8, #444]
	movw r10, #65535
	movt r10, #0
	str r10, [r8, #448]
	movw r10, #65280
	movt r10, #65535
	str r10, [r8, #452]
	movw r10, #65280
	movt r10, #65280
	str r10, [r8, #456]
	movw r10, #65535
	movt r10, #65280
	str r10, [r8, #460]
	movw r10, #0
	movt r10, #65280
	str r10, [r8, #464]
	movw r10, #255
	movt r10, #65280
	str r10, [r8, #468]
	movw r10, #65535
	movt r10, #0
	str r10, [r8, #472]
	movw r10, #255
	movt r10, #65535
	str r10, [r8, #476]
	movw r10, #65280
	movt r10, #65535
	str r10, [r8, #480]
	movw r10, #65280
	movt r10, #255
	str r10, [r8, #484]
	movw r10, #65535
	movt r10, #65280
	str r10, [r8, #488]
	movw r10, #65280
	movt r10, #0
	str r10, [r8, #492]
	movw r10, #65535
	movt r10, #255
	str r10, [r8, #496]
	movw r10, #65280
	movt r10, #65280
	str r10, [r8, #500]
	movw r10, #65535
	movt r10, #255
	str r10, [r8, #504]
	movw r10, #65280
	movt r10, #65280
	str r10, [r8, #508]
	movw r10, #65535
	movt r10, #255
	str r10, [r8, #512]
	movw r10, #65280
	movt r10, #255
	str r10, [r8, #516]
	movw r10, #0
	movt r10, #65535
	str r10, [r8, #520]
	movw r10, #0
	movt r10, #65535
	str r10, [r8, #524]
	movw r10, #65535
	movt r10, #65280
	str r10, [r8, #528]
	movw r10, #255
	movt r10, #255
	str r10, [r8, #532]
	movw r10, #65535
	movt r10, #255
	str r10, [r8, #536]
	movw r10, #65535
	movt r10, #0
	str r10, [r8, #540]
	movw r10, #65280
	movt r10, #255
	str r10, [r8, #544]
	movw r10, #0
	movt r10, #65535
	str r10, [r8, #548]
	movw r10, #65280
	movt r10, #255
	str r10, [r8, #552]
	movw r10, #0
	movt r10, #65280
	str r10, [r8, #556]
	movw r10, #255
	movt r10, #65280
	str r10, [r8, #560]
	movw r10, #65280
	movt r10, #65535
	str r10, [r8, #564]
	movw r10, #65280
	movt r10, #65280
	str r10, [r8, #568]
	movw r10, #65280
	movt r10, #65280
	str r10, [r8, #572]
	movw r10, #0
	movt r10, #65535
	str r10, [r8, #576]
	movw r10, #255
	movt r10, #0
	str r10, [r8, #580]
	movw r10, #255
	movt r10, #65535
	str r10, [r8, #584]
	movw r10, #65535
	movt r10, #65535
	str r10, [r8, #588]
	movw r10, #255
	movt r10, #65280
	str r10, [r8, #592]
	movw r10, #65280
	movt r10, #255
	str r10, [r8, #596]
	movw r10, #65535
	movt r10, #0
	str r10, [r8, #600]
	movw r10, #255
	movt r10, #0
	str r10, [r8, #604]
	movw r10, #0
	movt r10, #0
	str r10, [r8, #608]
	movw r10, #65280
	movt r10, #65280
	str r10, [r8, #612]
	movw r10, #65280
	movt r10, #0
	str r10, [r8, #616]
	movw r10, #0
	movt r10, #255
	str r10, [r8, #620]
	movw r10, #65535
	movt r10, #0
	str r10, [r8, #624]
	movw r10, #255
	movt r10, #0
	str r10, [r8, #628]
	movw r10, #65280
	movt r10, #65280
	str r10, [r8, #632]
	movw r10, #255
	movt r10, #65535
	str r10, [r8, #636]
	movw r10, #255
	movt r10, #65535
	str r10, [r8, #640]
	movw r10, #65535
	movt r10, #0
	str r10, [r8, #644]
	movw r10, #65280
	movt r10, #65280
	str r10, [r8, #648]
	movw r10, #0
	movt r10, #65280
	str r10, [r8, #652]
	movw r10, #255
	movt r10, #65280
	str r10, [r8, #656]
	movw r10, #65535
	movt r10, #65280
	str r10, [r8, #660]
	movw r10, #65280
	movt r10, #65535
	str r10, [r8, #664]
	movw r10, #65535
	movt r10, #65535
	str r10, [r8, #668]
	ldr r10, [r0, #0]
	str r10, [r8, #2528]
	ldr r10, [r0, #4]
	str r10, [r8, #2532]
	ldr r10, [r0, #8]
	str r10, [r8, #2536]
	ldr r10, [r0, #12]
	str r10, [r8, #2540]
	cmp r1, #16
	beq 20f
	ldr r10, [r0, #16]
	str r10, [r8, #2544]
	ldr r10, [r0, #20]
	str r10, [r8, #2548]
	cmp r1, #24
	beq 22f
	ldr r10, [r0, #24]
	str r10, [r8, #2552]
	ldr r10, [r0, #28]
	str r10, [r8, #2556]
	b 23f
22:
	mov r12, #0
	sub r12, r12, #1
	ldr r10, [r0, #16]
	eor r10, r10, r12
	str r10, [r8, #2552]
	ldr r10, [r0, #20]
	eor r10, r10, r12
	str r10, [r8, #2556]
23:
	b 21f
20:
	mov r10, #0
	str r10, [r8, #2544]
	str r10, [r8, #2548]
	str r10, [r8, #2552]
	str r10, [r8, #2556]
21:
	add r9, r8, #288
	ldr r10, [r8, #2528]
	str r10, [r8, #2560]
	ldr r10, [r8, #2532]
	str r10, [r8, #2564]
	ldr r10, [r8, #2536]
	str r10, [r8, #2568]
	ldr r10, [r8, #2540]
	str r10, [r8, #2572]
	ldr r10, [r8, #2544]
	ldr r11, [r8, #2560]
	eor r10, r10, r11
	str r10, [r8, #2560]
	ldr r10, [r8, #2548]
	ldr r11, [r8, #2564]
	eor r10, r10, r11
	str r10, [r8, #2564]
	ldr r10, [r8, #2552]
	ldr r11, [r8, #2568]
	eor r10, r10, r11
	str r10, [r8, #2568]
	ldr r10, [r8, #2556]
	ldr r11, [r8, #2572]
	eor r10, r10, r11
	str r10, [r8, #2572]
	mov r10, #3
	str r10, [r8, #2464]
24:
	ldr r0, [r8, #2560]
	mov r1, r0
	mov r2, r0
	mov r3, r0
	mov r4, r0
	mov r5, r0
	mov r6, r0
	mov r7, r0
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #160]
	str r1, [r8, #164]
	str r2, [r8, #168]
	str r3, [r8, #172]
	str r4, [r8, #176]
	str r5, [r8, #180]
	str r6, [r8, #184]
	str r7, [r8, #188]
	ldr r0, [r8, #2564]
	mov r1, r0
	mov r2, r0
	mov r3, r0
	mov r4, r0
	mov r5, r0
	mov r6, r0
	mov r7, r0
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #192]
	str r1, [r8, #196]
	str r2, [r8, #200]
	str r3, [r8, #204]
	str r4, [r8, #208]
	str r5, [r8, #212]
	str r6, [r8, #216]
	str r7, [r8, #220]
	ldr r0, [r8, #2568]
	mov r1, r0
	mov r2, r0
	mov r3, r0
	mov r4, r0
	mov r5, r0
	mov r6, r0
	mov r7, r0
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #224]
	str r1, [r8, #228]
	str r2, [r8, #232]
	str r3, [r8, #236]
	str r4, [r8, #240]
	str r5, [r8, #244]
	str r6, [r8, #248]
	str r7, [r8, #252]
	ldr r0, [r8, #2572]
	mov r1, r0
	mov r2, r0
	mov r3, r0
	mov r4, r0
	mov r5, r0
	mov r6, r0
	mov r7, r0
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #256]
	str r1, [r8, #260]
	str r2, [r8, #264]
	str r3, [r8, #268]
	str r4, [r8, #272]
	str r5, [r8, #276]
	str r6, [r8, #280]
	str r7, [r8, #284]
	ldr r0, [r8, #160]
	ldr r10, [r9, #0]
	eor r0, r0, r10
	ldr r1, [r8, #164]
	ldr r10, [r9, #4]
	eor r1, r1, r10
	ldr r2, [r8, #168]
	ldr r10, [r9, #8]
	eor r2, r2, r10
	ldr r3, [r8, #172]
	ldr r10, [r9, #12]
	eor r3, r3, r10
	ldr r4, [r8, #176]
	ldr r10, [r9, #16]
	eor r4, r4, r10
	ldr r5, [r8, #180]
	ldr r10, [r9, #20]
	eor r5, r5, r10
	ldr r6, [r8, #184]
	ldr r10, [r9, #24]
	eor r6, r6, r10
	ldr r7, [r8, #188]
	ldr r10, [r9, #28]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #4278190080
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #4278190080
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #4278190080
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #4278190080
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #4278190080
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #4278190080
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #4278190080
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #4278190080
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #65280
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #65280
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #16711680
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #16711680
	eor r7, r7, r10
	str r0, [r8, #128]
	str r1, [r8, #132]
	str r2, [r8, #136]
	str r3, [r8, #140]
	str r4, [r8, #144]
	str r5, [r8, #148]
	str r6, [r8, #152]
	str r7, [r8, #156]
	ldr r0, [r8, #192]
	ldr r10, [r9, #32]
	eor r0, r0, r10
	ldr r1, [r8, #196]
	ldr r10, [r9, #36]
	eor r1, r1, r10
	ldr r2, [r8, #200]
	ldr r10, [r9, #40]
	eor r2, r2, r10
	ldr r3, [r8, #204]
	ldr r10, [r9, #44]
	eor r3, r3, r10
	ldr r4, [r8, #208]
	ldr r10, [r9, #48]
	eor r4, r4, r10
	ldr r5, [r8, #212]
	ldr r10, [r9, #52]
	eor r5, r5, r10
	ldr r6, [r8, #216]
	ldr r10, [r9, #56]
	eor r6, r6, r10
	ldr r7, [r8, #220]
	ldr r10, [r9, #60]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #16711680
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #16711680
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #255
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #255
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #255
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #255
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #255
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #255
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #255
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #255
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #65280
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #65280
	eor r7, r7, r10
	ldr r11, [r8, #128]
	eor r11, r11, r0
	eor r11, r11, r0, ror #16
	eor r0, r0, r11
	eor r0, r0, r11, ror #8
	eor r11, r11, r0, ror #16
	ldr r10, [r8, #224]
	eor r10, r10, r11
	str r10, [r8, #224]
	ldr r10, [r8, #256]
	eor r10, r10, r0
	str r10, [r8, #256]
	ldr r11, [r8, #132]
	eor r11, r11, r1
	eor r11, r11, r1, ror #16
	eor r1, r1, r11
	eor r1, r1, r11, ror #8
	eor r11, r11, r1, ror #16
	ldr r10, [r8, #228]
	eor r10, r10, r11
	str r10, [r8, #228]
	ldr r10, [r8, #260]
	eor r10, r10, r1
	str r10, [r8, #260]
	ldr r11, [r8, #136]
	eor r11, r11, r2
	eor r11, r11, r2, ror #16
	eor r2, r2, r11
	eor r2, r2, r11, ror #8
	eor r11, r11, r2, ror #16
	ldr r10, [r8, #232]
	eor r10, r10, r11
	str r10, [r8, #232]
	ldr r10, [r8, #264]
	eor r10, r10, r2
	str r10, [r8, #264]
	ldr r11, [r8, #140]
	eor r11, r11, r3
	eor r11, r11, r3, ror #16
	eor r3, r3, r11
	eor r3, r3, r11, ror #8
	eor r11, r11, r3, ror #16
	ldr r10, [r8, #236]
	eor r10, r10, r11
	str r10, [r8, #236]
	ldr r10, [r8, #268]
	eor r10, r10, r3
	str r10, [r8, #268]
	ldr r11, [r8, #144]
	eor r11, r11, r4
	eor r11, r11, r4, ror #16
	eor r4, r4, r11
	eor r4, r4, r11, ror #8
	eor r11, r11, r4, ror #16
	ldr r10, [r8, #240]
	eor r10, r10, r11
	str r10, [r8, #240]
	ldr r10, [r8, #272]
	eor r10, r10, r4
	str r10, [r8, #272]
	ldr r11, [r8, #148]
	eor r11, r11, r5
	eor r11, r11, r5, ror #16
	eor r5, r5, r11
	eor r5, r5, r11, ror #8
	eor r11, r11, r5, ror #16
	ldr r10, [r8, #244]
	eor r10, r10, r11
	str r10, [r8, #244]
	ldr r10, [r8, #276]
	eor r10, r10, r5
	str r10, [r8, #276]
	ldr r11, [r8, #152]
	eor r11, r11, r6
	eor r11, r11, r6, ror #16
	eor r6, r6, r11
	eor r6, r6, r11, ror #8
	eor r11, r11, r6, ror #16
	ldr r10, [r8, #248]
	eor r10, r10, r11
	str r10, [r8, #248]
	ldr r10, [r8, #280]
	eor r10, r10, r6
	str r10, [r8, #280]
	ldr r11, [r8, #156]
	eor r11, r11, r7
	eor r11, r11, r7, ror #16
	eor r7, r7, r11
	eor r7, r7, r11, ror #8
	eor r11, r11, r7, ror #16
	ldr r10, [r8, #252]
	eor r10, r10, r11
	str r10, [r8, #252]
	ldr r10, [r8, #284]
	eor r10, r10, r7
	str r10, [r8, #284]
	ldr r0, [r8, #224]
	ldr r10, [r9, #64]
	eor r0, r0, r10
	ldr r1, [r8, #228]
	ldr r10, [r9, #68]
	eor r1, r1, r10
	ldr r2, [r8, #232]
	ldr r10, [r9, #72]
	eor r2, r2, r10
	ldr r3, [r8, #236]
	ldr r10, [r9, #76]
	eor r3, r3, r10
	ldr r4, [r8, #240]
	ldr r10, [r9, #80]
	eor r4, r4, r10
	ldr r5, [r8, #244]
	ldr r10, [r9, #84]
	eor r5, r5, r10
	ldr r6, [r8, #248]
	ldr r10, [r9, #88]
	eor r6, r6, r10
	ldr r7, [r8, #252]
	ldr r10, [r9, #92]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #4278190080
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #4278190080
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #4278190080
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #4278190080
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #4278190080
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #4278190080
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #4278190080
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #4278190080
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #65280
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #65280
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #16711680
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #16711680
	eor r7, r7, r10
	str r0, [r8, #128]
	str r1, [r8, #132]
	str r2, [r8, #136]
	str r3, [r8, #140]
	str r4, [r8, #144]
	str r5, [r8, #148]
	str r6, [r8, #152]
	str r7, [r8, #156]
	ldr r0, [r8, #256]
	ldr r10, [r9, #96]
	eor r0, r0, r10
	ldr r1, [r8, #260]
	ldr r10, [r9, #100]
	eor r1, r1, r10
	ldr r2, [r8, #264]
	ldr r10, [r9, #104]
	eor r2, r2, r10
	ldr r3, [r8, #268]
	ldr r10, [r9, #108]
	eor r3, r3, r10
	ldr r4, [r8, #272]
	ldr r10, [r9, #112]
	eor r4, r4, r10
	ldr r5, [r8, #276]
	ldr r10, [r9, #116]
	eor r5, r5, r10
	ldr r6, [r8, #280]
	ldr r10, [r9, #120]
	eor r6, r6, r10
	ldr r7, [r8, #284]
	ldr r10, [r9, #124]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #16711680
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #16711680
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #255
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #255
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #255
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #255
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #255
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #255
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #255
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #255
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #65280
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #65280
	eor r7, r7, r10
	ldr r11, [r8, #128]
	eor r11, r11, r0
	eor r11, r11, r0, ror #16
	eor r0, r0, r11
	eor r0, r0, r11, ror #8
	eor r11, r11, r0, ror #16
	ldr r10, [r8, #160]
	eor r10, r10, r11
	str r10, [r8, #160]
	ldr r10, [r8, #192]
	eor r10, r10, r0
	str r10, [r8, #192]
	ldr r11, [r8, #132]
	eor r11, r11, r1
	eor r11, r11, r1, ror #16
	eor r1, r1, r11
	eor r1, r1, r11, ror #8
	eor r11, r11, r1, ror #16
	ldr r10, [r8, #164]
	eor r10, r10, r11
	str r10, [r8, #164]
	ldr r10, [r8, #196]
	eor r10, r10, r1
	str r10, [r8, #196]
	ldr r11, [r8, #136]
	eor r11, r11, r2
	eor r11, r11, r2, ror #16
	eor r2, r2, r11
	eor r2, r2, r11, ror #8
	eor r11, r11, r2, ror #16
	ldr r10, [r8, #168]
	eor r10, r10, r11
	str r10, [r8, #168]
	ldr r10, [r8, #200]
	eor r10, r10, r2
	str r10, [r8, #200]
	ldr r11, [r8, #140]
	eor r11, r11, r3
	eor r11, r11, r3, ror #16
	eor r3, r3, r11
	eor r3, r3, r11, ror #8
	eor r11, r11, r3, ror #16
	ldr r10, [r8, #172]
	eor r10, r10, r11
	str r10, [r8, #172]
	ldr r10, [r8, #204]
	eor r10, r10, r3
	str r10, [r8, #204]
	ldr r11, [r8, #144]
	eor r11, r11, r4
	eor r11, r11, r4, ror #16
	eor r4, r4, r11
	eor r4, r4, r11, ror #8
	eor r11, r11, r4, ror #16
	ldr r10, [r8, #176]
	eor r10, r10, r11
	str r10, [r8, #176]
	ldr r10, [r8, #208]
	eor r10, r10, r4
	str r10, [r8, #208]
	ldr r11, [r8, #148]
	eor r11, r11, r5
	eor r11, r11, r5, ror #16
	eor r5, r5, r11
	eor r5, r5, r11, ror #8
	eor r11, r11, r5, ror #16
	ldr r10, [r8, #180]
	eor r10, r10, r11
	str r10, [r8, #180]
	ldr r10, [r8, #212]
	eor r10, r10, r5
	str r10, [r8, #212]
	ldr r11, [r8, #152]
	eor r11, r11, r6
	eor r11, r11, r6, ror #16
	eor r6, r6, r11
	eor r6, r6, r11, ror #8
	eor r11, r11, r6, ror #16
	ldr r10, [r8, #184]
	eor r10, r10, r11
	str r10, [r8, #184]
	ldr r10, [r8, #216]
	eor r10, r10, r6
	str r10, [r8, #216]
	ldr r11, [r8, #156]
	eor r11, r11, r7
	eor r11, r11, r7, ror #16
	eor r7, r7, r11
	eor r7, r7, r11, ror #8
	eor r11, r11, r7, ror #16
	ldr r10, [r8, #188]
	eor r10, r10, r11
	str r10, [r8, #188]
	ldr r10, [r8, #220]
	eor r10, r10, r7
	str r10, [r8, #220]
	ldr r0, [r8, #160]
	ldr r1, [r8, #164]
	ldr r2, [r8, #168]
	ldr r3, [r8, #172]
	ldr r4, [r8, #176]
	ldr r5, [r8, #180]
	ldr r6, [r8, #184]
	ldr r7, [r8, #188]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2560]
	ldr r0, [r8, #192]
	ldr r1, [r8, #196]
	ldr r2, [r8, #200]
	ldr r3, [r8, #204]
	ldr r4, [r8, #208]
	ldr r5, [r8, #212]
	ldr r6, [r8, #216]
	ldr r7, [r8, #220]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2564]
	ldr r0, [r8, #224]
	ldr r1, [r8, #228]
	ldr r2, [r8, #232]
	ldr r3, [r8, #236]
	ldr r4, [r8, #240]
	ldr r5, [r8, #244]
	ldr r6, [r8, #248]
	ldr r7, [r8, #252]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2568]
	ldr r0, [r8, #256]
	ldr r1, [r8, #260]
	ldr r2, [r8, #264]
	ldr r3, [r8, #268]
	ldr r4, [r8, #272]
	ldr r5, [r8, #276]
	ldr r6, [r8, #280]
	ldr r7, [r8, #284]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2572]
	add r9, r9, #128
	ldr r10, [r8, #2464]
	lsr r11, r10, #1
	cmp r11, #0
	bne 25f
	ldr r10, [r8, #2560]
	str r10, [r8, #2592]
	ldr r10, [r8, #2564]
	str r10, [r8, #2596]
	ldr r10, [r8, #2568]
	str r10, [r8, #2600]
	ldr r10, [r8, #2572]
	str r10, [r8, #2604]
	b 26f
25:
	cmp r10, #3
	beq 27f
	ldr r10, [r8, #2560]
	str r10, [r8, #2576]
	ldr r10, [r8, #2564]
	str r10, [r8, #2580]
	ldr r10, [r8, #2568]
	str r10, [r8, #2584]
	ldr r10, [r8, #2572]
	str r10, [r8, #2588]
	ldr r10, [r8, #2544]
	ldr r11, [r8, #2560]
	eor r10, r10, r11
	str r10, [r8, #2560]
	ldr r10, [r8, #2548]
	ldr r11, [r8, #2564]
	eor r10, r10, r11
	str r10, [r8, #2564]
	ldr r10, [r8, #2552]
	ldr r11, [r8, #2568]
	eor r10, r10, r11
	str r10, [r8, #2568]
	ldr r10, [r8, #2556]
	ldr r11, [r8, #2572]
	eor r10, r10, r11
	str r10, [r8, #2572]
	b 28f
27:
	ldr r10, [r8, #2528]
	ldr r11, [r8, #2560]
	eor r10, r10, r11
	str r10, [r8, #2560]
	ldr r10, [r8, #2532]
	ldr r11, [r8, #2564]
	eor r10, r10, r11
	str r10, [r8, #2564]
	ldr r10, [r8, #2536]
	ldr r11, [r8, #2568]
	eor r10, r10, r11
	str r10, [r8, #2568]
	ldr r10, [r8, #2540]
	ldr r11, [r8, #2572]
	eor r10, r10, r11
	str r10, [r8, #2572]
28:
26:
	ldr r10, [r8, #2464]
	subs r10, r10, #1
	str r10, [r8, #2464]
	bne 24b
	ldr r10, [r8, #2528]
	rev r10, r10
	str r10, [r8, #2528]
	ldr r10, [r8, #2532]
	rev r10, r10
	str r10, [r8, #2532]
	ldr r10, [r8, #2536]
	rev r10, r10
	str r10, [r8, #2536]
	ldr r10, [r8, #2540]
	rev r10, r10
	str r10, [r8, #2540]
	ldr r10, [r8, #2544]
	rev r10, r10
	str r10, [r8, #2544]
	ldr r10, [r8, #2548]
	rev r10, r10
	str r10, [r8, #2548]
	ldr r10, [r8, #2552]
	rev r10, r10
	str r10, [r8, #2552]
	ldr r10, [r8, #2556]
	rev r10, r10
	str r10, [r8, #2556]
	ldr r10, [r8, #2576]
	rev r10, r10
	str r10, [r8, #2576]
	ldr r10, [r8, #2580]
	rev r10, r10
	str r10, [r8, #2580]
	ldr r10, [r8, #2584]
	rev r10, r10
	str r10, [r8, #2584]
	ldr r10, [r8, #2588]
	rev r10, r10
	str r10, [r8, #2588]
	ldr r10, [r8, #2592]
	rev r10, r10
	str r10, [r8, #2592]
	ldr r10, [r8, #2596]
	rev r10, r10
	str r10, [r8, #2596]
	ldr r10, [r8, #2600]
	rev r10, r10
	str r10, [r8, #2600]
	ldr r10, [r8, #2604]
	rev r10, r10
	str r10, [r8, #2604]
	ldr r2, [r8, #2508]
	ldr r10, [r8, #2512]
	cmp r10, #16
	beq 29f
	ldr r10, [r8, #2528]
	rev r10, r10
	str r10, [r2, #0]
	ldr r10, [r8, #2532]
	rev r10, r10
	str r10, [r2, #4]
	ldr r10, [r8, #2536]
	rev r10, r10
	str r10, [r2, #8]
	ldr r10, [r8, #2540]
	rev r10, r10
	str r10, [r2, #12]
	ldr r10, [r8, #2592]
	rev r10, r10
	str r10, [r2, #16]
	ldr r10, [r8, #2596]
	rev r10, r10
	str r10, [r2, #20]
	ldr r10, [r8, #2600]
	rev r10, r10
	str r10, [r2, #24]
	ldr r10, [r8, #2604]
	rev r10, r10
	str r10, [r2, #28]
	ldr r10, [r8, #2544]
	ldr r11, [r8, #2548]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #32]
	ldr r10, [r8, #2548]
	ldr r11, [r8, #2552]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #36]
	ldr r10, [r8, #2552]
	ldr r11, [r8, #2556]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #40]
	ldr r10, [r8, #2556]
	ldr r11, [r8, #2544]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #44]
	ldr r10, [r8, #2576]
	ldr r11, [r8, #2580]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #48]
	ldr r10, [r8, #2580]
	ldr r11, [r8, #2584]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #52]
	ldr r10, [r8, #2584]
	ldr r11, [r8, #2588]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #56]
	ldr r10, [r8, #2588]
	ldr r11, [r8, #2576]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #60]
	ldr r10, [r8, #2544]
	ldr r11, [r8, #2548]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #64]
	ldr r10, [r8, #2548]
	ldr r11, [r8, #2552]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #68]
	ldr r10, [r8, #2552]
	ldr r11, [r8, #2556]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #72]
	ldr r10, [r8, #2556]
	ldr r11, [r8, #2544]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #76]
	ldr r10, [r8, #2592]
	ldr r11, [r8, #2596]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #80]
	ldr r10, [r8, #2596]
	ldr r11, [r8, #2600]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #84]
	ldr r10, [r8, #2600]
	ldr r11, [r8, #2604]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #88]
	ldr r10, [r8, #2604]
	ldr r11, [r8, #2592]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #92]
	ldr r10, [r8, #2532]
	ldr r11, [r8, #2536]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #96]
	ldr r10, [r8, #2536]
	ldr r11, [r8, #2540]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #100]
	ldr r10, [r8, #2540]
	ldr r11, [r8, #2528]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #104]
	ldr r10, [r8, #2528]
	ldr r11, [r8, #2532]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #108]
	ldr r10, [r8, #2580]
	ldr r11, [r8, #2584]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #112]
	ldr r10, [r8, #2584]
	ldr r11, [r8, #2588]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #116]
	ldr r10, [r8, #2588]
	ldr r11, [r8, #2576]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #120]
	ldr r10, [r8, #2576]
	ldr r11, [r8, #2580]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #124]
	ldr r10, [r8, #2532]
	ldr r11, [r8, #2536]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #128]
	ldr r10, [r8, #2536]
	ldr r11, [r8, #2540]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #132]
	ldr r10, [r8, #2540]
	ldr r11, [r8, #2528]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #136]
	ldr r10, [r8, #2528]
	ldr r11, [r8, #2532]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #140]
	ldr r10, [r8, #2548]
	ldr r11, [r8, #2552]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #144]
	ldr r10, [r8, #2552]
	ldr r11, [r8, #2556]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #148]
	ldr r10, [r8, #2556]
	ldr r11, [r8, #2544]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #152]
	ldr r10, [r8, #2544]
	ldr r11, [r8, #2548]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #156]
	ldr r10, [r8, #2596]
	ldr r11, [r8, #2600]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #160]
	ldr r10, [r8, #2600]
	ldr r11, [r8, #2604]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #164]
	ldr r10, [r8, #2604]
	ldr r11, [r8, #2592]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #168]
	ldr r10, [r8, #2592]
	ldr r11, [r8, #2596]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #172]
	ldr r10, [r8, #2536]
	ldr r11, [r8, #2540]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #176]
	ldr r10, [r8, #2540]
	ldr r11, [r8, #2528]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #180]
	ldr r10, [r8, #2528]
	ldr r11, [r8, #2532]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #184]
	ldr r10, [r8, #2532]
	ldr r11, [r8, #2536]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #188]
	ldr r10, [r8, #2584]
	ldr r11, [r8, #2588]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #192]
	ldr r10, [r8, #2588]
	ldr r11, [r8, #2576]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #196]
	ldr r10, [r8, #2576]
	ldr r11, [r8, #2580]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #200]
	ldr r10, [r8, #2580]
	ldr r11, [r8, #2584]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #204]
	ldr r10, [r8, #2552]
	ldr r11, [r8, #2556]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #208]
	ldr r10, [r8, #2556]
	ldr r11, [r8, #2544]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #212]
	ldr r10, [r8, #2544]
	ldr r11, [r8, #2548]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #216]
	ldr r10, [r8, #2548]
	ldr r11, [r8, #2552]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #220]
	ldr r10, [r8, #2584]
	ldr r11, [r8, #2588]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #224]
	ldr r10, [r8, #2588]
	ldr r11, [r8, #2576]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #228]
	ldr r10, [r8, #2576]
	ldr r11, [r8, #2580]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #232]
	ldr r10, [r8, #2580]
	ldr r11, [r8, #2584]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #236]
	ldr r10, [r8, #2540]
	ldr r11, [r8, #2528]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #240]
	ldr r10, [r8, #2528]
	ldr r11, [r8, #2532]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #244]
	ldr r10, [r8, #2532]
	ldr r11, [r8, #2536]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #248]
	ldr r10, [r8, #2536]
	ldr r11, [r8, #2540]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #252]
	ldr r10, [r8, #2604]
	ldr r11, [r8, #2592]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #256]
	ldr r10, [r8, #2592]
	ldr r11, [r8, #2596]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #260]
	ldr r10, [r8, #2596]
	ldr r11, [r8, #2600]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #264]
	ldr r10, [r8, #2600]
	ldr r11, [r8, #2604]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #268]
	b 210f
29:
	ldr r10, [r8, #2528]
	rev r10, r10
	str r10, [r2, #0]
	ldr r10, [r8, #2532]
	rev r10, r10
	str r10, [r2, #4]
	ldr r10, [r8, #2536]
	rev r10, r10
	str r10, [r2, #8]
	ldr r10, [r8, #2540]
	rev r10, r10
	str r10, [r2, #12]
	ldr r10, [r8, #2576]
	rev r10, r10
	str r10, [r2, #16]
	ldr r10, [r8, #2580]
	rev r10, r10
	str r10, [r2, #20]
	ldr r10, [r8, #2584]
	rev r10, r10
	str r10, [r2, #24]
	ldr r10, [r8, #2588]
	rev r10, r10
	str r10, [r2, #28]
	ldr r10, [r8, #2528]
	ldr r11, [r8, #2532]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #32]
	ldr r10, [r8, #2532]
	ldr r11, [r8, #2536]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #36]
	ldr r10, [r8, #2536]
	ldr r11, [r8, #2540]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #40]
	ldr r10, [r8, #2540]
	ldr r11, [r8, #2528]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #44]
	ldr r10, [r8, #2576]
	ldr r11, [r8, #2580]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #48]
	ldr r10, [r8, #2580]
	ldr r11, [r8, #2584]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #52]
	ldr r10, [r8, #2584]
	ldr r11, [r8, #2588]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #56]
	ldr r10, [r8, #2588]
	ldr r11, [r8, #2576]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #60]
	ldr r10, [r8, #2576]
	ldr r11, [r8, #2580]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #64]
	ldr r10, [r8, #2580]
	ldr r11, [r8, #2584]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #68]
	ldr r10, [r8, #2584]
	ldr r11, [r8, #2588]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #72]
	ldr r10, [r8, #2588]
	ldr r11, [r8, #2576]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #76]
	ldr r10, [r8, #2532]
	ldr r11, [r8, #2536]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #80]
	ldr r10, [r8, #2536]
	ldr r11, [r8, #2540]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #84]
	ldr r10, [r8, #2540]
	ldr r11, [r8, #2528]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #88]
	ldr r10, [r8, #2528]
	ldr r11, [r8, #2532]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #92]
	ldr r10, [r8, #2580]
	ldr r11, [r8, #2584]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #96]
	ldr r10, [r8, #2584]
	ldr r11, [r8, #2588]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #100]
	ldr r10, [r8, #2540]
	ldr r11, [r8, #2528]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #104]
	ldr r10, [r8, #2528]
	ldr r11, [r8, #2532]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #108]
	ldr r10, [r8, #2580]
	ldr r11, [r8, #2584]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #112]
	ldr r10, [r8, #2584]
	ldr r11, [r8, #2588]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #116]
	ldr r10, [r8, #2588]
	ldr r11, [r8, #2576]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #120]
	ldr r10, [r8, #2576]
	ldr r11, [r8, #2580]
	lsl r10, r10, #28
	orr r10, r10, r11, lsr #4
	rev r10, r10
	str r10, [r2, #124]
	ldr r10, [r8, #2536]
	ldr r11, [r8, #2540]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #128]
	ldr r10, [r8, #2540]
	ldr r11, [r8, #2528]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #132]
	ldr r10, [r8, #2528]
	ldr r11, [r8, #2532]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #136]
	ldr r10, [r8, #2532]
	ldr r11, [r8, #2536]
	lsl r10, r10, #13
	orr r10, r10, r11, lsr #19
	rev r10, r10
	str r10, [r2, #140]
	ldr r10, [r8, #2536]
	ldr r11, [r8, #2540]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #144]
	ldr r10, [r8, #2540]
	ldr r11, [r8, #2528]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #148]
	ldr r10, [r8, #2528]
	ldr r11, [r8, #2532]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #152]
	ldr r10, [r8, #2532]
	ldr r11, [r8, #2536]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #156]
	ldr r10, [r8, #2584]
	ldr r11, [r8, #2588]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #160]
	ldr r10, [r8, #2588]
	ldr r11, [r8, #2576]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #164]
	ldr r10, [r8, #2576]
	ldr r11, [r8, #2580]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #168]
	ldr r10, [r8, #2580]
	ldr r11, [r8, #2584]
	lsl r10, r10, #30
	orr r10, r10, r11, lsr #2
	rev r10, r10
	str r10, [r2, #172]
	ldr r10, [r8, #2540]
	ldr r11, [r8, #2528]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #176]
	ldr r10, [r8, #2528]
	ldr r11, [r8, #2532]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #180]
	ldr r10, [r8, #2532]
	ldr r11, [r8, #2536]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #184]
	ldr r10, [r8, #2536]
	ldr r11, [r8, #2540]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #188]
	ldr r10, [r8, #2588]
	ldr r11, [r8, #2576]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #192]
	ldr r10, [r8, #2576]
	ldr r11, [r8, #2580]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #196]
	ldr r10, [r8, #2580]
	ldr r11, [r8, #2584]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #200]
	ldr r10, [r8, #2584]
	ldr r11, [r8, #2588]
	lsl r10, r10, #15
	orr r10, r10, r11, lsr #17
	rev r10, r10
	str r10, [r2, #204]
210:
	mov r12, r8
	ldr r4, [r12, #2472]
	ldr r5, [r12, #2476]
	ldr r6, [r12, #2480]
	ldr r7, [r12, #2484]
	ldr r8, [r12, #2488]
	ldr r9, [r12, #2492]
	ldr r10, [r12, #2496]
	ldr r11, [r12, #2500]
	ldr lr, [r12, #2504]
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	str r2, [r12, #32]
	str r2, [r12, #36]
	str r2, [r12, #40]
	str r2, [r12, #44]
	str r2, [r12, #48]
	str r2, [r12, #52]
	str r2, [r12, #56]
	str r2, [r12, #60]
	str r2, [r12, #64]
	str r2, [r12, #68]
	str r2, [r12, #72]
	str r2, [r12, #76]
	str r2, [r12, #80]
	str r2, [r12, #84]
	str r2, [r12, #88]
	str r2, [r12, #92]
	str r2, [r12, #96]
	str r2, [r12, #100]
	str r2, [r12, #104]
	str r2, [r12, #108]
	str r2, [r12, #112]
	str r2, [r12, #116]
	str r2, [r12, #120]
	str r2, [r12, #124]
	str r2, [r12, #128]
	str r2, [r12, #132]
	str r2, [r12, #136]
	str r2, [r12, #140]
	str r2, [r12, #144]
	str r2, [r12, #148]
	str r2, [r12, #152]
	str r2, [r12, #156]
	str r2, [r12, #160]
	str r2, [r12, #164]
	str r2, [r12, #168]
	str r2, [r12, #172]
	str r2, [r12, #176]
	str r2, [r12, #180]
	str r2, [r12, #184]
	str r2, [r12, #188]
	str r2, [r12, #192]
	str r2, [r12, #196]
	str r2, [r12, #200]
	str r2, [r12, #204]
	str r2, [r12, #208]
	str r2, [r12, #212]
	str r2, [r12, #216]
	str r2, [r12, #220]
	str r2, [r12, #224]
	str r2, [r12, #228]
	str r2, [r12, #232]
	str r2, [r12, #236]
	str r2, [r12, #240]
	str r2, [r12, #244]
	str r2, [r12, #248]
	str r2, [r12, #252]
	str r2, [r12, #256]
	str r2, [r12, #260]
	str r2, [r12, #264]
	str r2, [r12, #268]
	str r2, [r12, #272]
	str r2, [r12, #276]
	str r2, [r12, #280]
	str r2, [r12, #284]
	str r2, [r12, #288]
	str r2, [r12, #292]
	str r2, [r12, #296]
	str r2, [r12, #300]
	str r2, [r12, #304]
	str r2, [r12, #308]
	str r2, [r12, #312]
	str r2, [r12, #316]
	str r2, [r12, #320]
	str r2, [r12, #324]
	str r2, [r12, #328]
	str r2, [r12, #332]
	str r2, [r12, #336]
	str r2, [r12, #340]
	str r2, [r12, #344]
	str r2, [r12, #348]
	str r2, [r12, #352]
	str r2, [r12, #356]
	str r2, [r12, #360]
	str r2, [r12, #364]
	str r2, [r12, #368]
	str r2, [r12, #372]
	str r2, [r12, #376]
	str r2, [r12, #380]
	str r2, [r12, #384]
	str r2, [r12, #388]
	str r2, [r12, #392]
	str r2, [r12, #396]
	str r2, [r12, #400]
	str r2, [r12, #404]
	str r2, [r12, #408]
	str r2, [r12, #412]
	str r2, [r12, #416]
	str r2, [r12, #420]
	str r2, [r12, #424]
	str r2, [r12, #428]
	str r2, [r12, #432]
	str r2, [r12, #436]
	str r2, [r12, #440]
	str r2, [r12, #444]
	str r2, [r12, #448]
	str r2, [r12, #452]
	str r2, [r12, #456]
	str r2, [r12, #460]
	str r2, [r12, #464]
	str r2, [r12, #468]
	str r2, [r12, #472]
	str r2, [r12, #476]
	str r2, [r12, #480]
	str r2, [r12, #484]
	str r2, [r12, #488]
	str r2, [r12, #492]
	str r2, [r12, #496]
	str r2, [r12, #500]
	str r2, [r12, #504]
	str r2, [r12, #508]
	str r2, [r12, #512]
	str r2, [r12, #516]
	str r2, [r12, #520]
	str r2, [r12, #524]
	str r2, [r12, #528]
	str r2, [r12, #532]
	str r2, [r12, #536]
	str r2, [r12, #540]
	str r2, [r12, #544]
	str r2, [r12, #548]
	str r2, [r12, #552]
	str r2, [r12, #556]
	str r2, [r12, #560]
	str r2, [r12, #564]
	str r2, [r12, #568]
	str r2, [r12, #572]
	str r2, [r12, #576]
	str r2, [r12, #580]
	str r2, [r12, #584]
	str r2, [r12, #588]
	str r2, [r12, #592]
	str r2, [r12, #596]
	str r2, [r12, #600]
	str r2, [r12, #604]
	str r2, [r12, #608]
	str r2, [r12, #612]
	str r2, [r12, #616]
	str r2, [r12, #620]
	str r2, [r12, #624]
	str r2, [r12, #628]
	str r2, [r12, #632]
	str r2, [r12, #636]
	str r2, [r12, #640]
	str r2, [r12, #644]
	str r2, [r12, #648]
	str r2, [r12, #652]
	str r2, [r12, #656]
	str r2, [r12, #660]
	str r2, [r12, #664]
	str r2, [r12, #668]
	str r2, [r12, #672]
	str r2, [r12, #676]
	str r2, [r12, #680]
	str r2, [r12, #684]
	str r2, [r12, #688]
	str r2, [r12, #692]
	str r2, [r12, #696]
	str r2, [r12, #700]
	str r2, [r12, #704]
	str r2, [r12, #708]
	str r2, [r12, #712]
	str r2, [r12, #716]
	str r2, [r12, #720]
	str r2, [r12, #724]
	str r2, [r12, #728]
	str r2, [r12, #732]
	str r2, [r12, #736]
	str r2, [r12, #740]
	str r2, [r12, #744]
	str r2, [r12, #748]
	str r2, [r12, #752]
	str r2, [r12, #756]
	str r2, [r12, #760]
	str r2, [r12, #764]
	str r2, [r12, #768]
	str r2, [r12, #772]
	str r2, [r12, #776]
	str r2, [r12, #780]
	str r2, [r12, #784]
	str r2, [r12, #788]
	str r2, [r12, #792]
	str r2, [r12, #796]
	str r2, [r12, #800]
	str r2, [r12, #804]
	str r2, [r12, #808]
	str r2, [r12, #812]
	str r2, [r12, #816]
	str r2, [r12, #820]
	str r2, [r12, #824]
	str r2, [r12, #828]
	str r2, [r12, #832]
	str r2, [r12, #836]
	str r2, [r12, #840]
	str r2, [r12, #844]
	str r2, [r12, #848]
	str r2, [r12, #852]
	str r2, [r12, #856]
	str r2, [r12, #860]
	str r2, [r12, #864]
	str r2, [r12, #868]
	str r2, [r12, #872]
	str r2, [r12, #876]
	str r2, [r12, #880]
	str r2, [r12, #884]
	str r2, [r12, #888]
	str r2, [r12, #892]
	str r2, [r12, #896]
	str r2, [r12, #900]
	str r2, [r12, #904]
	str r2, [r12, #908]
	str r2, [r12, #912]
	str r2, [r12, #916]
	str r2, [r12, #920]
	str r2, [r12, #924]
	str r2, [r12, #928]
	str r2, [r12, #932]
	str r2, [r12, #936]
	str r2, [r12, #940]
	str r2, [r12, #944]
	str r2, [r12, #948]
	str r2, [r12, #952]
	str r2, [r12, #956]
	str r2, [r12, #960]
	str r2, [r12, #964]
	str r2, [r12, #968]
	str r2, [r12, #972]
	str r2, [r12, #976]
	str r2, [r12, #980]
	str r2, [r12, #984]
	str r2, [r12, #988]
	str r2, [r12, #992]
	str r2, [r12, #996]
	str r2, [r12, #1000]
	str r2, [r12, #1004]
	str r2, [r12, #1008]
	str r2, [r12, #1012]
	str r2, [r12, #1016]
	str r2, [r12, #1020]
	str r2, [r12, #1024]
	str r2, [r12, #1028]
	str r2, [r12, #1032]
	str r2, [r12, #1036]
	str r2, [r12, #1040]
	str r2, [r12, #1044]
	str r2, [r12, #1048]
	str r2, [r12, #1052]
	str r2, [r12, #1056]
	str r2, [r12, #1060]
	str r2, [r12, #1064]
	str r2, [r12, #1068]
	str r2, [r12, #1072]
	str r2, [r12, #1076]
	str r2, [r12, #1080]
	str r2, [r12, #1084]
	str r2, [r12, #1088]
	str r2, [r12, #1092]
	str r2, [r12, #1096]
	str r2, [r12, #1100]
	str r2, [r12, #1104]
	str r2, [r12, #1108]
	str r2, [r12, #1112]
	str r2, [r12, #1116]
	str r2, [r12, #1120]
	str r2, [r12, #1124]
	str r2, [r12, #1128]
	str r2, [r12, #1132]
	str r2, [r12, #1136]
	str r2, [r12, #1140]
	str r2, [r12, #1144]
	str r2, [r12, #1148]
	str r2, [r12, #1152]
	str r2, [r12, #1156]
	str r2, [r12, #1160]
	str r2, [r12, #1164]
	str r2, [r12, #1168]
	str r2, [r12, #1172]
	str r2, [r12, #1176]
	str r2, [r12, #1180]
	str r2, [r12, #1184]
	str r2, [r12, #1188]
	str r2, [r12, #1192]
	str r2, [r12, #1196]
	str r2, [r12, #1200]
	str r2, [r12, #1204]
	str r2, [r12, #1208]
	str r2, [r12, #1212]
	str r2, [r12, #1216]
	str r2, [r12, #1220]
	str r2, [r12, #1224]
	str r2, [r12, #1228]
	str r2, [r12, #1232]
	str r2, [r12, #1236]
	str r2, [r12, #1240]
	str r2, [r12, #1244]
	str r2, [r12, #1248]
	str r2, [r12, #1252]
	str r2, [r12, #1256]
	str r2, [r12, #1260]
	str r2, [r12, #1264]
	str r2, [r12, #1268]
	str r2, [r12, #1272]
	str r2, [r12, #1276]
	str r2, [r12, #1280]
	str r2, [r12, #1284]
	str r2, [r12, #1288]
	str r2, [r12, #1292]
	str r2, [r12, #1296]
	str r2, [r12, #1300]
	str r2, [r12, #1304]
	str r2, [r12, #1308]
	str r2, [r12, #1312]
	str r2, [r12, #1316]
	str r2, [r12, #1320]
	str r2, [r12, #1324]
	str r2, [r12, #1328]
	str r2, [r12, #1332]
	str r2, [r12, #1336]
	str r2, [r12, #1340]
	str r2, [r12, #1344]
	str r2, [r12, #1348]
	str r2, [r12, #1352]
	str r2, [r12, #1356]
	str r2, [r12, #1360]
	str r2, [r12, #1364]
	str r2, [r12, #1368]
	str r2, [r12, #1372]
	str r2, [r12, #1376]
	str r2, [r12, #1380]
	str r2, [r12, #1384]
	str r2, [r12, #1388]
	str r2, [r12, #1392]
	str r2, [r12, #1396]
	str r2, [r12, #1400]
	str r2, [r12, #1404]
	str r2, [r12, #1408]
	str r2, [r12, #1412]
	str r2, [r12, #1416]
	str r2, [r12, #1420]
	str r2, [r12, #1424]
	str r2, [r12, #1428]
	str r2, [r12, #1432]
	str r2, [r12, #1436]
	str r2, [r12, #1440]
	str r2, [r12, #1444]
	str r2, [r12, #1448]
	str r2, [r12, #1452]
	str r2, [r12, #1456]
	str r2, [r12, #1460]
	str r2, [r12, #1464]
	str r2, [r12, #1468]
	str r2, [r12, #1472]
	str r2, [r12, #1476]
	str r2, [r12, #1480]
	str r2, [r12, #1484]
	str r2, [r12, #1488]
	str r2, [r12, #1492]
	str r2, [r12, #1496]
	str r2, [r12, #1500]
	str r2, [r12, #1504]
	str r2, [r12, #1508]
	str r2, [r12, #1512]
	str r2, [r12, #1516]
	str r2, [r12, #1520]
	str r2, [r12, #1524]
	str r2, [r12, #1528]
	str r2, [r12, #1532]
	str r2, [r12, #1536]
	str r2, [r12, #1540]
	str r2, [r12, #1544]
	str r2, [r12, #1548]
	str r2, [r12, #1552]
	str r2, [r12, #1556]
	str r2, [r12, #1560]
	str r2, [r12, #1564]
	str r2, [r12, #1568]
	str r2, [r12, #1572]
	str r2, [r12, #1576]
	str r2, [r12, #1580]
	str r2, [r12, #1584]
	str r2, [r12, #1588]
	str r2, [r12, #1592]
	str r2, [r12, #1596]
	str r2, [r12, #1600]
	str r2, [r12, #1604]
	str r2, [r12, #1608]
	str r2, [r12, #1612]
	str r2, [r12, #1616]
	str r2, [r12, #1620]
	str r2, [r12, #1624]
	str r2, [r12, #1628]
	str r2, [r12, #1632]
	str r2, [r12, #1636]
	str r2, [r12, #1640]
	str r2, [r12, #1644]
	str r2, [r12, #1648]
	str r2, [r12, #1652]
	str r2, [r12, #1656]
	str r2, [r12, #1660]
	str r2, [r12, #1664]
	str r2, [r12, #1668]
	str r2, [r12, #1672]
	str r2, [r12, #1676]
	str r2, [r12, #1680]
	str r2, [r12, #1684]
	str r2, [r12, #1688]
	str r2, [r12, #1692]
	str r2, [r12, #1696]
	str r2, [r12, #1700]
	str r2, [r12, #1704]
	str r2, [r12, #1708]
	str r2, [r12, #1712]
	str r2, [r12, #1716]
	str r2, [r12, #1720]
	str r2, [r12, #1724]
	str r2, [r12, #1728]
	str r2, [r12, #1732]
	str r2, [r12, #1736]
	str r2, [r12, #1740]
	str r2, [r12, #1744]
	str r2, [r12, #1748]
	str r2, [r12, #1752]
	str r2, [r12, #1756]
	str r2, [r12, #1760]
	str r2, [r12, #1764]
	str r2, [r12, #1768]
	str r2, [r12, #1772]
	str r2, [r12, #1776]
	str r2, [r12, #1780]
	str r2, [r12, #1784]
	str r2, [r12, #1788]
	str r2, [r12, #1792]
	str r2, [r12, #1796]
	str r2, [r12, #1800]
	str r2, [r12, #1804]
	str r2, [r12, #1808]
	str r2, [r12, #1812]
	str r2, [r12, #1816]
	str r2, [r12, #1820]
	str r2, [r12, #1824]
	str r2, [r12, #1828]
	str r2, [r12, #1832]
	str r2, [r12, #1836]
	str r2, [r12, #1840]
	str r2, [r12, #1844]
	str r2, [r12, #1848]
	str r2, [r12, #1852]
	str r2, [r12, #1856]
	str r2, [r12, #1860]
	str r2, [r12, #1864]
	str r2, [r12, #1868]
	str r2, [r12, #1872]
	str r2, [r12, #1876]
	str r2, [r12, #1880]
	str r2, [r12, #1884]
	str r2, [r12, #1888]
	str r2, [r12, #1892]
	str r2, [r12, #1896]
	str r2, [r12, #1900]
	str r2, [r12, #1904]
	str r2, [r12, #1908]
	str r2, [r12, #1912]
	str r2, [r12, #1916]
	str r2, [r12, #1920]
	str r2, [r12, #1924]
	str r2, [r12, #1928]
	str r2, [r12, #1932]
	str r2, [r12, #1936]
	str r2, [r12, #1940]
	str r2, [r12, #1944]
	str r2, [r12, #1948]
	str r2, [r12, #1952]
	str r2, [r12, #1956]
	str r2, [r12, #1960]
	str r2, [r12, #1964]
	str r2, [r12, #1968]
	str r2, [r12, #1972]
	str r2, [r12, #1976]
	str r2, [r12, #1980]
	str r2, [r12, #1984]
	str r2, [r12, #1988]
	str r2, [r12, #1992]
	str r2, [r12, #1996]
	str r2, [r12, #2000]
	str r2, [r12, #2004]
	str r2, [r12, #2008]
	str r2, [r12, #2012]
	str r2, [r12, #2016]
	str r2, [r12, #2020]
	str r2, [r12, #2024]
	str r2, [r12, #2028]
	str r2, [r12, #2032]
	str r2, [r12, #2036]
	str r2, [r12, #2040]
	str r2, [r12, #2044]
	str r2, [r12, #2048]
	str r2, [r12, #2052]
	str r2, [r12, #2056]
	str r2, [r12, #2060]
	str r2, [r12, #2064]
	str r2, [r12, #2068]
	str r2, [r12, #2072]
	str r2, [r12, #2076]
	str r2, [r12, #2080]
	str r2, [r12, #2084]
	str r2, [r12, #2088]
	str r2, [r12, #2092]
	str r2, [r12, #2096]
	str r2, [r12, #2100]
	str r2, [r12, #2104]
	str r2, [r12, #2108]
	str r2, [r12, #2112]
	str r2, [r12, #2116]
	str r2, [r12, #2120]
	str r2, [r12, #2124]
	str r2, [r12, #2128]
	str r2, [r12, #2132]
	str r2, [r12, #2136]
	str r2, [r12, #2140]
	str r2, [r12, #2144]
	str r2, [r12, #2148]
	str r2, [r12, #2152]
	str r2, [r12, #2156]
	str r2, [r12, #2160]
	str r2, [r12, #2164]
	str r2, [r12, #2168]
	str r2, [r12, #2172]
	str r2, [r12, #2176]
	str r2, [r12, #2180]
	str r2, [r12, #2184]
	str r2, [r12, #2188]
	str r2, [r12, #2192]
	str r2, [r12, #2196]
	str r2, [r12, #2200]
	str r2, [r12, #2204]
	str r2, [r12, #2208]
	str r2, [r12, #2212]
	str r2, [r12, #2216]
	str r2, [r12, #2220]
	str r2, [r12, #2224]
	str r2, [r12, #2228]
	str r2, [r12, #2232]
	str r2, [r12, #2236]
	str r2, [r12, #2240]
	str r2, [r12, #2244]
	str r2, [r12, #2248]
	str r2, [r12, #2252]
	str r2, [r12, #2256]
	str r2, [r12, #2260]
	str r2, [r12, #2264]
	str r2, [r12, #2268]
	str r2, [r12, #2272]
	str r2, [r12, #2276]
	str r2, [r12, #2280]
	str r2, [r12, #2284]
	str r2, [r12, #2288]
	str r2, [r12, #2292]
	str r2, [r12, #2296]
	str r2, [r12, #2300]
	str r2, [r12, #2304]
	str r2, [r12, #2308]
	str r2, [r12, #2312]
	str r2, [r12, #2316]
	str r2, [r12, #2320]
	str r2, [r12, #2324]
	str r2, [r12, #2328]
	str r2, [r12, #2332]
	str r2, [r12, #2336]
	str r2, [r12, #2340]
	str r2, [r12, #2344]
	str r2, [r12, #2348]
	str r2, [r12, #2352]
	str r2, [r12, #2356]
	str r2, [r12, #2360]
	str r2, [r12, #2364]
	str r2, [r12, #2368]
	str r2, [r12, #2372]
	str r2, [r12, #2376]
	str r2, [r12, #2380]
	str r2, [r12, #2384]
	str r2, [r12, #2388]
	str r2, [r12, #2392]
	str r2, [r12, #2396]
	str r2, [r12, #2400]
	str r2, [r12, #2404]
	str r2, [r12, #2408]
	str r2, [r12, #2412]
	str r2, [r12, #2416]
	str r2, [r12, #2420]
	str r2, [r12, #2424]
	str r2, [r12, #2428]
	str r2, [r12, #2432]
	str r2, [r12, #2436]
	str r2, [r12, #2440]
	str r2, [r12, #2444]
	str r2, [r12, #2448]
	str r2, [r12, #2452]
	str r2, [r12, #2456]
	str r2, [r12, #2460]
	str r2, [r12, #2464]
	str r2, [r12, #2468]
	str r2, [r12, #2472]
	str r2, [r12, #2476]
	str r2, [r12, #2480]
	str r2, [r12, #2484]
	str r2, [r12, #2488]
	str r2, [r12, #2492]
	str r2, [r12, #2496]
	str r2, [r12, #2500]
	str r2, [r12, #2504]
	str r2, [r12, #2508]
	str r2, [r12, #2512]
	str r2, [r12, #2516]
	str r2, [r12, #2520]
	str r2, [r12, #2524]
	str r2, [r12, #2528]
	str r2, [r12, #2532]
	str r2, [r12, #2536]
	str r2, [r12, #2540]
	str r2, [r12, #2544]
	str r2, [r12, #2548]
	str r2, [r12, #2552]
	str r2, [r12, #2556]
	str r2, [r12, #2560]
	str r2, [r12, #2564]
	str r2, [r12, #2568]
	str r2, [r12, #2572]
	str r2, [r12, #2576]
	str r2, [r12, #2580]
	str r2, [r12, #2584]
	str r2, [r12, #2588]
	str r2, [r12, #2592]
	str r2, [r12, #2596]
	str r2, [r12, #2600]
	str r2, [r12, #2604]
	str r2, [r12, #2608]
	str r2, [r12, #2612]
	str r2, [r12, #2616]
	str r2, [r12, #2620]
	str r2, [r12, #2624]
	str r2, [r12, #2628]
	str r2, [r12, #2632]
	str r2, [r12, #2636]
	str r2, [r12, #2640]
	str r2, [r12, #2644]
	str r2, [r12, #2648]
	str r2, [r12, #2652]
	str r2, [r12, #2656]
	str r2, [r12, #2660]
	str r2, [r12, #2664]
	str r2, [r12, #2668]
	str r2, [r12, #2672]
	str r2, [r12, #2676]
	str r2, [r12, #2680]
	str r2, [r12, #2684]
	str r2, [r12, #2688]
	str r2, [r12, #2692]
	str r2, [r12, #2696]
	str r2, [r12, #2700]
	str r2, [r12, #2704]
	str r2, [r12, #2708]
	str r2, [r12, #2712]
	str r2, [r12, #2716]
	add sp, sp, #2720
	bx lr

vg_camellia_ecb_encrypt:
	sub sp, sp, #2816
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
	str r4, [r12, #2472]
	str r5, [r12, #2476]
	str r6, [r12, #2480]
	str r7, [r12, #2484]
	str r8, [r12, #2488]
	str r9, [r12, #2492]
	str r10, [r12, #2496]
	str r11, [r12, #2500]
	str lr, [r12, #2504]
	mov r8, r12
	mov r12, r0
	cmp r1, #18
	mov r1, r2
	mov r2, r3
	beq 20f
	mov lr, #34
	b 21f
20:
	mov lr, #26
21:
	add r9, r8, #288
22:
	ldr r4, [r12, #0]
	movw r11, #257
	movt r11, #257
	and r5, r11, r4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #0]
	and r5, r11, r4, lsr #1
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #4]
	and r5, r11, r4, lsr #2
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #8]
	and r5, r11, r4, lsr #3
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #12]
	and r5, r11, r4, lsr #4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #16]
	and r5, r11, r4, lsr #5
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #20]
	and r5, r11, r4, lsr #6
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #24]
	and r5, r11, r4, lsr #7
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #28]
	ldr r4, [r12, #4]
	movw r11, #257
	movt r11, #257
	and r5, r11, r4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #32]
	and r5, r11, r4, lsr #1
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #36]
	and r5, r11, r4, lsr #2
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #40]
	and r5, r11, r4, lsr #3
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #44]
	and r5, r11, r4, lsr #4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #48]
	and r5, r11, r4, lsr #5
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #52]
	and r5, r11, r4, lsr #6
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #56]
	and r5, r11, r4, lsr #7
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #60]
	add r9, r9, #64
	add r12, r12, #8
	subs lr, lr, #1
	bne 22b
	sub lr, r9, #128
	cmp r2, #0
	beq 23f
25:
	lsr r10, r2, #3
	cmp r10, #0
	bne 26f
	mov r3, r2
	b 27f
26:
	mov r3, #8
27:
	mov r0, r1
	add r12, r8, #2528
28:
	ldr r10, [r0, #0]
	str r10, [r12, #0]
	ldr r10, [r0, #4]
	str r10, [r12, #4]
	ldr r10, [r0, #8]
	str r10, [r12, #8]
	ldr r10, [r0, #12]
	str r10, [r12, #12]
	add r0, r0, #16
	add r12, r12, #16
	subs r3, r3, #1
	bne 28b
	str r1, [r8, #2508]
	str r2, [r8, #2512]
	str lr, [r8, #2468]
	add r12, r8, #2528
	ldr r0, [r12, #0]
	ldr r1, [r12, #16]
	ldr r2, [r12, #32]
	ldr r3, [r12, #48]
	ldr r4, [r12, #64]
	ldr r5, [r12, #80]
	ldr r6, [r12, #96]
	ldr r7, [r12, #112]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #160]
	str r1, [r8, #164]
	str r2, [r8, #168]
	str r3, [r8, #172]
	str r4, [r8, #176]
	str r5, [r8, #180]
	str r6, [r8, #184]
	str r7, [r8, #188]
	ldr r0, [r12, #4]
	ldr r1, [r12, #20]
	ldr r2, [r12, #36]
	ldr r3, [r12, #52]
	ldr r4, [r12, #68]
	ldr r5, [r12, #84]
	ldr r6, [r12, #100]
	ldr r7, [r12, #116]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #192]
	str r1, [r8, #196]
	str r2, [r8, #200]
	str r3, [r8, #204]
	str r4, [r8, #208]
	str r5, [r8, #212]
	str r6, [r8, #216]
	str r7, [r8, #220]
	ldr r0, [r12, #8]
	ldr r1, [r12, #24]
	ldr r2, [r12, #40]
	ldr r3, [r12, #56]
	ldr r4, [r12, #72]
	ldr r5, [r12, #88]
	ldr r6, [r12, #104]
	ldr r7, [r12, #120]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #224]
	str r1, [r8, #228]
	str r2, [r8, #232]
	str r3, [r8, #236]
	str r4, [r8, #240]
	str r5, [r8, #244]
	str r6, [r8, #248]
	str r7, [r8, #252]
	ldr r0, [r12, #12]
	ldr r1, [r12, #28]
	ldr r2, [r12, #44]
	ldr r3, [r12, #60]
	ldr r4, [r12, #76]
	ldr r5, [r12, #92]
	ldr r6, [r12, #108]
	ldr r7, [r12, #124]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #256]
	str r1, [r8, #260]
	str r2, [r8, #264]
	str r3, [r8, #268]
	str r4, [r8, #272]
	str r5, [r8, #276]
	str r6, [r8, #280]
	str r7, [r8, #284]
	add r9, r8, #288
	ldr r11, [r8, #160]
	ldr r10, [r9, #0]
	eor r11, r11, r10
	str r11, [r8, #160]
	ldr r11, [r8, #164]
	ldr r10, [r9, #4]
	eor r11, r11, r10
	str r11, [r8, #164]
	ldr r11, [r8, #168]
	ldr r10, [r9, #8]
	eor r11, r11, r10
	str r11, [r8, #168]
	ldr r11, [r8, #172]
	ldr r10, [r9, #12]
	eor r11, r11, r10
	str r11, [r8, #172]
	ldr r11, [r8, #176]
	ldr r10, [r9, #16]
	eor r11, r11, r10
	str r11, [r8, #176]
	ldr r11, [r8, #180]
	ldr r10, [r9, #20]
	eor r11, r11, r10
	str r11, [r8, #180]
	ldr r11, [r8, #184]
	ldr r10, [r9, #24]
	eor r11, r11, r10
	str r11, [r8, #184]
	ldr r11, [r8, #188]
	ldr r10, [r9, #28]
	eor r11, r11, r10
	str r11, [r8, #188]
	ldr r11, [r8, #192]
	ldr r10, [r9, #32]
	eor r11, r11, r10
	str r11, [r8, #192]
	ldr r11, [r8, #196]
	ldr r10, [r9, #36]
	eor r11, r11, r10
	str r11, [r8, #196]
	ldr r11, [r8, #200]
	ldr r10, [r9, #40]
	eor r11, r11, r10
	str r11, [r8, #200]
	ldr r11, [r8, #204]
	ldr r10, [r9, #44]
	eor r11, r11, r10
	str r11, [r8, #204]
	ldr r11, [r8, #208]
	ldr r10, [r9, #48]
	eor r11, r11, r10
	str r11, [r8, #208]
	ldr r11, [r8, #212]
	ldr r10, [r9, #52]
	eor r11, r11, r10
	str r11, [r8, #212]
	ldr r11, [r8, #216]
	ldr r10, [r9, #56]
	eor r11, r11, r10
	str r11, [r8, #216]
	ldr r11, [r8, #220]
	ldr r10, [r9, #60]
	eor r11, r11, r10
	str r11, [r8, #220]
	ldr r11, [r8, #224]
	ldr r10, [r9, #64]
	eor r11, r11, r10
	str r11, [r8, #224]
	ldr r11, [r8, #228]
	ldr r10, [r9, #68]
	eor r11, r11, r10
	str r11, [r8, #228]
	ldr r11, [r8, #232]
	ldr r10, [r9, #72]
	eor r11, r11, r10
	str r11, [r8, #232]
	ldr r11, [r8, #236]
	ldr r10, [r9, #76]
	eor r11, r11, r10
	str r11, [r8, #236]
	ldr r11, [r8, #240]
	ldr r10, [r9, #80]
	eor r11, r11, r10
	str r11, [r8, #240]
	ldr r11, [r8, #244]
	ldr r10, [r9, #84]
	eor r11, r11, r10
	str r11, [r8, #244]
	ldr r11, [r8, #248]
	ldr r10, [r9, #88]
	eor r11, r11, r10
	str r11, [r8, #248]
	ldr r11, [r8, #252]
	ldr r10, [r9, #92]
	eor r11, r11, r10
	str r11, [r8, #252]
	ldr r11, [r8, #256]
	ldr r10, [r9, #96]
	eor r11, r11, r10
	str r11, [r8, #256]
	ldr r11, [r8, #260]
	ldr r10, [r9, #100]
	eor r11, r11, r10
	str r11, [r8, #260]
	ldr r11, [r8, #264]
	ldr r10, [r9, #104]
	eor r11, r11, r10
	str r11, [r8, #264]
	ldr r11, [r8, #268]
	ldr r10, [r9, #108]
	eor r11, r11, r10
	str r11, [r8, #268]
	ldr r11, [r8, #272]
	ldr r10, [r9, #112]
	eor r11, r11, r10
	str r11, [r8, #272]
	ldr r11, [r8, #276]
	ldr r10, [r9, #116]
	eor r11, r11, r10
	str r11, [r8, #276]
	ldr r11, [r8, #280]
	ldr r10, [r9, #120]
	eor r11, r11, r10
	str r11, [r8, #280]
	ldr r11, [r8, #284]
	ldr r10, [r9, #124]
	eor r11, r11, r10
	str r11, [r8, #284]
	add r9, r9, #128
29:
	add r10, r9, #384
	str r10, [r8, #2464]
210:
	ldr r0, [r8, #160]
	ldr r10, [r9, #0]
	eor r0, r0, r10
	ldr r1, [r8, #164]
	ldr r10, [r9, #4]
	eor r1, r1, r10
	ldr r2, [r8, #168]
	ldr r10, [r9, #8]
	eor r2, r2, r10
	ldr r3, [r8, #172]
	ldr r10, [r9, #12]
	eor r3, r3, r10
	ldr r4, [r8, #176]
	ldr r10, [r9, #16]
	eor r4, r4, r10
	ldr r5, [r8, #180]
	ldr r10, [r9, #20]
	eor r5, r5, r10
	ldr r6, [r8, #184]
	ldr r10, [r9, #24]
	eor r6, r6, r10
	ldr r7, [r8, #188]
	ldr r10, [r9, #28]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #4278190080
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #4278190080
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #4278190080
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #4278190080
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #4278190080
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #4278190080
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #4278190080
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #4278190080
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #65280
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #65280
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #16711680
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #16711680
	eor r7, r7, r10
	str r0, [r8, #128]
	str r1, [r8, #132]
	str r2, [r8, #136]
	str r3, [r8, #140]
	str r4, [r8, #144]
	str r5, [r8, #148]
	str r6, [r8, #152]
	str r7, [r8, #156]
	ldr r0, [r8, #192]
	ldr r10, [r9, #32]
	eor r0, r0, r10
	ldr r1, [r8, #196]
	ldr r10, [r9, #36]
	eor r1, r1, r10
	ldr r2, [r8, #200]
	ldr r10, [r9, #40]
	eor r2, r2, r10
	ldr r3, [r8, #204]
	ldr r10, [r9, #44]
	eor r3, r3, r10
	ldr r4, [r8, #208]
	ldr r10, [r9, #48]
	eor r4, r4, r10
	ldr r5, [r8, #212]
	ldr r10, [r9, #52]
	eor r5, r5, r10
	ldr r6, [r8, #216]
	ldr r10, [r9, #56]
	eor r6, r6, r10
	ldr r7, [r8, #220]
	ldr r10, [r9, #60]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #16711680
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #16711680
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #255
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #255
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #255
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #255
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #255
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #255
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #255
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #255
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #65280
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #65280
	eor r7, r7, r10
	ldr r11, [r8, #128]
	eor r11, r11, r0
	eor r11, r11, r0, ror #16
	eor r0, r0, r11
	eor r0, r0, r11, ror #8
	eor r11, r11, r0, ror #16
	ldr r10, [r8, #224]
	eor r10, r10, r11
	str r10, [r8, #224]
	ldr r10, [r8, #256]
	eor r10, r10, r0
	str r10, [r8, #256]
	ldr r11, [r8, #132]
	eor r11, r11, r1
	eor r11, r11, r1, ror #16
	eor r1, r1, r11
	eor r1, r1, r11, ror #8
	eor r11, r11, r1, ror #16
	ldr r10, [r8, #228]
	eor r10, r10, r11
	str r10, [r8, #228]
	ldr r10, [r8, #260]
	eor r10, r10, r1
	str r10, [r8, #260]
	ldr r11, [r8, #136]
	eor r11, r11, r2
	eor r11, r11, r2, ror #16
	eor r2, r2, r11
	eor r2, r2, r11, ror #8
	eor r11, r11, r2, ror #16
	ldr r10, [r8, #232]
	eor r10, r10, r11
	str r10, [r8, #232]
	ldr r10, [r8, #264]
	eor r10, r10, r2
	str r10, [r8, #264]
	ldr r11, [r8, #140]
	eor r11, r11, r3
	eor r11, r11, r3, ror #16
	eor r3, r3, r11
	eor r3, r3, r11, ror #8
	eor r11, r11, r3, ror #16
	ldr r10, [r8, #236]
	eor r10, r10, r11
	str r10, [r8, #236]
	ldr r10, [r8, #268]
	eor r10, r10, r3
	str r10, [r8, #268]
	ldr r11, [r8, #144]
	eor r11, r11, r4
	eor r11, r11, r4, ror #16
	eor r4, r4, r11
	eor r4, r4, r11, ror #8
	eor r11, r11, r4, ror #16
	ldr r10, [r8, #240]
	eor r10, r10, r11
	str r10, [r8, #240]
	ldr r10, [r8, #272]
	eor r10, r10, r4
	str r10, [r8, #272]
	ldr r11, [r8, #148]
	eor r11, r11, r5
	eor r11, r11, r5, ror #16
	eor r5, r5, r11
	eor r5, r5, r11, ror #8
	eor r11, r11, r5, ror #16
	ldr r10, [r8, #244]
	eor r10, r10, r11
	str r10, [r8, #244]
	ldr r10, [r8, #276]
	eor r10, r10, r5
	str r10, [r8, #276]
	ldr r11, [r8, #152]
	eor r11, r11, r6
	eor r11, r11, r6, ror #16
	eor r6, r6, r11
	eor r6, r6, r11, ror #8
	eor r11, r11, r6, ror #16
	ldr r10, [r8, #248]
	eor r10, r10, r11
	str r10, [r8, #248]
	ldr r10, [r8, #280]
	eor r10, r10, r6
	str r10, [r8, #280]
	ldr r11, [r8, #156]
	eor r11, r11, r7
	eor r11, r11, r7, ror #16
	eor r7, r7, r11
	eor r7, r7, r11, ror #8
	eor r11, r11, r7, ror #16
	ldr r10, [r8, #252]
	eor r10, r10, r11
	str r10, [r8, #252]
	ldr r10, [r8, #284]
	eor r10, r10, r7
	str r10, [r8, #284]
	ldr r0, [r8, #224]
	ldr r10, [r9, #64]
	eor r0, r0, r10
	ldr r1, [r8, #228]
	ldr r10, [r9, #68]
	eor r1, r1, r10
	ldr r2, [r8, #232]
	ldr r10, [r9, #72]
	eor r2, r2, r10
	ldr r3, [r8, #236]
	ldr r10, [r9, #76]
	eor r3, r3, r10
	ldr r4, [r8, #240]
	ldr r10, [r9, #80]
	eor r4, r4, r10
	ldr r5, [r8, #244]
	ldr r10, [r9, #84]
	eor r5, r5, r10
	ldr r6, [r8, #248]
	ldr r10, [r9, #88]
	eor r6, r6, r10
	ldr r7, [r8, #252]
	ldr r10, [r9, #92]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #4278190080
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #4278190080
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #4278190080
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #4278190080
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #4278190080
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #4278190080
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #4278190080
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #4278190080
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #65280
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #65280
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #16711680
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #16711680
	eor r7, r7, r10
	str r0, [r8, #128]
	str r1, [r8, #132]
	str r2, [r8, #136]
	str r3, [r8, #140]
	str r4, [r8, #144]
	str r5, [r8, #148]
	str r6, [r8, #152]
	str r7, [r8, #156]
	ldr r0, [r8, #256]
	ldr r10, [r9, #96]
	eor r0, r0, r10
	ldr r1, [r8, #260]
	ldr r10, [r9, #100]
	eor r1, r1, r10
	ldr r2, [r8, #264]
	ldr r10, [r9, #104]
	eor r2, r2, r10
	ldr r3, [r8, #268]
	ldr r10, [r9, #108]
	eor r3, r3, r10
	ldr r4, [r8, #272]
	ldr r10, [r9, #112]
	eor r4, r4, r10
	ldr r5, [r8, #276]
	ldr r10, [r9, #116]
	eor r5, r5, r10
	ldr r6, [r8, #280]
	ldr r10, [r9, #120]
	eor r6, r6, r10
	ldr r7, [r8, #284]
	ldr r10, [r9, #124]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #16711680
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #16711680
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #255
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #255
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #255
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #255
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #255
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #255
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #255
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #255
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #65280
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #65280
	eor r7, r7, r10
	ldr r11, [r8, #128]
	eor r11, r11, r0
	eor r11, r11, r0, ror #16
	eor r0, r0, r11
	eor r0, r0, r11, ror #8
	eor r11, r11, r0, ror #16
	ldr r10, [r8, #160]
	eor r10, r10, r11
	str r10, [r8, #160]
	ldr r10, [r8, #192]
	eor r10, r10, r0
	str r10, [r8, #192]
	ldr r11, [r8, #132]
	eor r11, r11, r1
	eor r11, r11, r1, ror #16
	eor r1, r1, r11
	eor r1, r1, r11, ror #8
	eor r11, r11, r1, ror #16
	ldr r10, [r8, #164]
	eor r10, r10, r11
	str r10, [r8, #164]
	ldr r10, [r8, #196]
	eor r10, r10, r1
	str r10, [r8, #196]
	ldr r11, [r8, #136]
	eor r11, r11, r2
	eor r11, r11, r2, ror #16
	eor r2, r2, r11
	eor r2, r2, r11, ror #8
	eor r11, r11, r2, ror #16
	ldr r10, [r8, #168]
	eor r10, r10, r11
	str r10, [r8, #168]
	ldr r10, [r8, #200]
	eor r10, r10, r2
	str r10, [r8, #200]
	ldr r11, [r8, #140]
	eor r11, r11, r3
	eor r11, r11, r3, ror #16
	eor r3, r3, r11
	eor r3, r3, r11, ror #8
	eor r11, r11, r3, ror #16
	ldr r10, [r8, #172]
	eor r10, r10, r11
	str r10, [r8, #172]
	ldr r10, [r8, #204]
	eor r10, r10, r3
	str r10, [r8, #204]
	ldr r11, [r8, #144]
	eor r11, r11, r4
	eor r11, r11, r4, ror #16
	eor r4, r4, r11
	eor r4, r4, r11, ror #8
	eor r11, r11, r4, ror #16
	ldr r10, [r8, #176]
	eor r10, r10, r11
	str r10, [r8, #176]
	ldr r10, [r8, #208]
	eor r10, r10, r4
	str r10, [r8, #208]
	ldr r11, [r8, #148]
	eor r11, r11, r5
	eor r11, r11, r5, ror #16
	eor r5, r5, r11
	eor r5, r5, r11, ror #8
	eor r11, r11, r5, ror #16
	ldr r10, [r8, #180]
	eor r10, r10, r11
	str r10, [r8, #180]
	ldr r10, [r8, #212]
	eor r10, r10, r5
	str r10, [r8, #212]
	ldr r11, [r8, #152]
	eor r11, r11, r6
	eor r11, r11, r6, ror #16
	eor r6, r6, r11
	eor r6, r6, r11, ror #8
	eor r11, r11, r6, ror #16
	ldr r10, [r8, #184]
	eor r10, r10, r11
	str r10, [r8, #184]
	ldr r10, [r8, #216]
	eor r10, r10, r6
	str r10, [r8, #216]
	ldr r11, [r8, #156]
	eor r11, r11, r7
	eor r11, r11, r7, ror #16
	eor r7, r7, r11
	eor r7, r7, r11, ror #8
	eor r11, r11, r7, ror #16
	ldr r10, [r8, #188]
	eor r10, r10, r11
	str r10, [r8, #188]
	ldr r10, [r8, #220]
	eor r10, r10, r7
	str r10, [r8, #220]
	add r9, r9, #128
	ldr r10, [r8, #2464]
	cmp r9, r10
	bne 210b
	ldr r10, [r8, #2468]
	cmp r9, r10
	bne 211f
	b 212f
211:
	ldr r0, [r8, #224]
	ldr r1, [r8, #228]
	ldr r2, [r8, #232]
	ldr r3, [r8, #236]
	ldr r4, [r8, #240]
	ldr r5, [r8, #244]
	ldr r6, [r8, #248]
	ldr r7, [r8, #252]
	ldr r10, [r9, #96]
	ldr r11, [r8, #256]
	orr r10, r10, r11
	eor r0, r0, r10
	ldr r10, [r9, #100]
	ldr r11, [r8, #260]
	orr r10, r10, r11
	eor r1, r1, r10
	ldr r10, [r9, #104]
	ldr r11, [r8, #264]
	orr r10, r10, r11
	eor r2, r2, r10
	ldr r10, [r9, #108]
	ldr r11, [r8, #268]
	orr r10, r10, r11
	eor r3, r3, r10
	ldr r10, [r9, #112]
	ldr r11, [r8, #272]
	orr r10, r10, r11
	eor r4, r4, r10
	ldr r10, [r9, #116]
	ldr r11, [r8, #276]
	orr r10, r10, r11
	eor r5, r5, r10
	ldr r10, [r9, #120]
	ldr r11, [r8, #280]
	orr r10, r10, r11
	eor r6, r6, r10
	ldr r10, [r9, #124]
	ldr r11, [r8, #284]
	orr r10, r10, r11
	eor r7, r7, r10
	ldr r10, [r9, #92]
	and r10, r10, r7
	ldr r11, [r8, #256]
	eor r11, r11, r10, ror #8
	str r11, [r8, #256]
	ldr r10, [r9, #64]
	and r10, r10, r0
	ldr r11, [r8, #260]
	eor r11, r11, r10
	str r11, [r8, #260]
	ldr r10, [r9, #68]
	and r10, r10, r1
	ldr r11, [r8, #264]
	eor r11, r11, r10
	str r11, [r8, #264]
	ldr r10, [r9, #72]
	and r10, r10, r2
	ldr r11, [r8, #268]
	eor r11, r11, r10
	str r11, [r8, #268]
	ldr r10, [r9, #76]
	and r10, r10, r3
	ldr r11, [r8, #272]
	eor r11, r11, r10
	str r11, [r8, #272]
	ldr r10, [r9, #80]
	and r10, r10, r4
	ldr r11, [r8, #276]
	eor r11, r11, r10
	str r11, [r8, #276]
	ldr r10, [r9, #84]
	and r10, r10, r5
	ldr r11, [r8, #280]
	eor r11, r11, r10
	str r11, [r8, #280]
	ldr r10, [r9, #88]
	and r10, r10, r6
	ldr r11, [r8, #284]
	eor r11, r11, r10
	str r11, [r8, #284]
	str r0, [r8, #224]
	str r1, [r8, #228]
	str r2, [r8, #232]
	str r3, [r8, #236]
	str r4, [r8, #240]
	str r5, [r8, #244]
	str r6, [r8, #248]
	str r7, [r8, #252]
	ldr r0, [r8, #160]
	ldr r1, [r8, #164]
	ldr r2, [r8, #168]
	ldr r3, [r8, #172]
	ldr r4, [r8, #176]
	ldr r5, [r8, #180]
	ldr r6, [r8, #184]
	ldr r7, [r8, #188]
	ldr r10, [r9, #28]
	and r10, r10, r7
	ldr r11, [r8, #192]
	eor r11, r11, r10, ror #8
	str r11, [r8, #192]
	ldr r10, [r9, #0]
	and r10, r10, r0
	ldr r11, [r8, #196]
	eor r11, r11, r10
	str r11, [r8, #196]
	ldr r10, [r9, #4]
	and r10, r10, r1
	ldr r11, [r8, #200]
	eor r11, r11, r10
	str r11, [r8, #200]
	ldr r10, [r9, #8]
	and r10, r10, r2
	ldr r11, [r8, #204]
	eor r11, r11, r10
	str r11, [r8, #204]
	ldr r10, [r9, #12]
	and r10, r10, r3
	ldr r11, [r8, #208]
	eor r11, r11, r10
	str r11, [r8, #208]
	ldr r10, [r9, #16]
	and r10, r10, r4
	ldr r11, [r8, #212]
	eor r11, r11, r10
	str r11, [r8, #212]
	ldr r10, [r9, #20]
	and r10, r10, r5
	ldr r11, [r8, #216]
	eor r11, r11, r10
	str r11, [r8, #216]
	ldr r10, [r9, #24]
	and r10, r10, r6
	ldr r11, [r8, #220]
	eor r11, r11, r10
	str r11, [r8, #220]
	ldr r10, [r9, #32]
	ldr r11, [r8, #192]
	orr r10, r10, r11
	eor r0, r0, r10
	ldr r10, [r9, #36]
	ldr r11, [r8, #196]
	orr r10, r10, r11
	eor r1, r1, r10
	ldr r10, [r9, #40]
	ldr r11, [r8, #200]
	orr r10, r10, r11
	eor r2, r2, r10
	ldr r10, [r9, #44]
	ldr r11, [r8, #204]
	orr r10, r10, r11
	eor r3, r3, r10
	ldr r10, [r9, #48]
	ldr r11, [r8, #208]
	orr r10, r10, r11
	eor r4, r4, r10
	ldr r10, [r9, #52]
	ldr r11, [r8, #212]
	orr r10, r10, r11
	eor r5, r5, r10
	ldr r10, [r9, #56]
	ldr r11, [r8, #216]
	orr r10, r10, r11
	eor r6, r6, r10
	ldr r10, [r9, #60]
	ldr r11, [r8, #220]
	orr r10, r10, r11
	eor r7, r7, r10
	str r0, [r8, #160]
	str r1, [r8, #164]
	str r2, [r8, #168]
	str r3, [r8, #172]
	str r4, [r8, #176]
	str r5, [r8, #180]
	str r6, [r8, #184]
	str r7, [r8, #188]
	add r9, r9, #128
212:
	ldr r10, [r8, #2468]
	cmp r9, r10
	bne 29b
	ldr r11, [r8, #224]
	ldr r10, [r9, #0]
	eor r11, r11, r10
	str r11, [r8, #224]
	ldr r11, [r8, #228]
	ldr r10, [r9, #4]
	eor r11, r11, r10
	str r11, [r8, #228]
	ldr r11, [r8, #232]
	ldr r10, [r9, #8]
	eor r11, r11, r10
	str r11, [r8, #232]
	ldr r11, [r8, #236]
	ldr r10, [r9, #12]
	eor r11, r11, r10
	str r11, [r8, #236]
	ldr r11, [r8, #240]
	ldr r10, [r9, #16]
	eor r11, r11, r10
	str r11, [r8, #240]
	ldr r11, [r8, #244]
	ldr r10, [r9, #20]
	eor r11, r11, r10
	str r11, [r8, #244]
	ldr r11, [r8, #248]
	ldr r10, [r9, #24]
	eor r11, r11, r10
	str r11, [r8, #248]
	ldr r11, [r8, #252]
	ldr r10, [r9, #28]
	eor r11, r11, r10
	str r11, [r8, #252]
	ldr r11, [r8, #256]
	ldr r10, [r9, #32]
	eor r11, r11, r10
	str r11, [r8, #256]
	ldr r11, [r8, #260]
	ldr r10, [r9, #36]
	eor r11, r11, r10
	str r11, [r8, #260]
	ldr r11, [r8, #264]
	ldr r10, [r9, #40]
	eor r11, r11, r10
	str r11, [r8, #264]
	ldr r11, [r8, #268]
	ldr r10, [r9, #44]
	eor r11, r11, r10
	str r11, [r8, #268]
	ldr r11, [r8, #272]
	ldr r10, [r9, #48]
	eor r11, r11, r10
	str r11, [r8, #272]
	ldr r11, [r8, #276]
	ldr r10, [r9, #52]
	eor r11, r11, r10
	str r11, [r8, #276]
	ldr r11, [r8, #280]
	ldr r10, [r9, #56]
	eor r11, r11, r10
	str r11, [r8, #280]
	ldr r11, [r8, #284]
	ldr r10, [r9, #60]
	eor r11, r11, r10
	str r11, [r8, #284]
	ldr r11, [r8, #160]
	ldr r10, [r9, #64]
	eor r11, r11, r10
	str r11, [r8, #160]
	ldr r11, [r8, #164]
	ldr r10, [r9, #68]
	eor r11, r11, r10
	str r11, [r8, #164]
	ldr r11, [r8, #168]
	ldr r10, [r9, #72]
	eor r11, r11, r10
	str r11, [r8, #168]
	ldr r11, [r8, #172]
	ldr r10, [r9, #76]
	eor r11, r11, r10
	str r11, [r8, #172]
	ldr r11, [r8, #176]
	ldr r10, [r9, #80]
	eor r11, r11, r10
	str r11, [r8, #176]
	ldr r11, [r8, #180]
	ldr r10, [r9, #84]
	eor r11, r11, r10
	str r11, [r8, #180]
	ldr r11, [r8, #184]
	ldr r10, [r9, #88]
	eor r11, r11, r10
	str r11, [r8, #184]
	ldr r11, [r8, #188]
	ldr r10, [r9, #92]
	eor r11, r11, r10
	str r11, [r8, #188]
	ldr r11, [r8, #192]
	ldr r10, [r9, #96]
	eor r11, r11, r10
	str r11, [r8, #192]
	ldr r11, [r8, #196]
	ldr r10, [r9, #100]
	eor r11, r11, r10
	str r11, [r8, #196]
	ldr r11, [r8, #200]
	ldr r10, [r9, #104]
	eor r11, r11, r10
	str r11, [r8, #200]
	ldr r11, [r8, #204]
	ldr r10, [r9, #108]
	eor r11, r11, r10
	str r11, [r8, #204]
	ldr r11, [r8, #208]
	ldr r10, [r9, #112]
	eor r11, r11, r10
	str r11, [r8, #208]
	ldr r11, [r8, #212]
	ldr r10, [r9, #116]
	eor r11, r11, r10
	str r11, [r8, #212]
	ldr r11, [r8, #216]
	ldr r10, [r9, #120]
	eor r11, r11, r10
	str r11, [r8, #216]
	ldr r11, [r8, #220]
	ldr r10, [r9, #124]
	eor r11, r11, r10
	str r11, [r8, #220]
	ldr r0, [r8, #224]
	ldr r1, [r8, #228]
	ldr r2, [r8, #232]
	ldr r3, [r8, #236]
	ldr r4, [r8, #240]
	ldr r5, [r8, #244]
	ldr r6, [r8, #248]
	ldr r7, [r8, #252]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2528]
	str r1, [r8, #2544]
	str r2, [r8, #2560]
	str r3, [r8, #2576]
	str r4, [r8, #2592]
	str r5, [r8, #2608]
	str r6, [r8, #2624]
	str r7, [r8, #2640]
	ldr r0, [r8, #256]
	ldr r1, [r8, #260]
	ldr r2, [r8, #264]
	ldr r3, [r8, #268]
	ldr r4, [r8, #272]
	ldr r5, [r8, #276]
	ldr r6, [r8, #280]
	ldr r7, [r8, #284]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2532]
	str r1, [r8, #2548]
	str r2, [r8, #2564]
	str r3, [r8, #2580]
	str r4, [r8, #2596]
	str r5, [r8, #2612]
	str r6, [r8, #2628]
	str r7, [r8, #2644]
	ldr r0, [r8, #160]
	ldr r1, [r8, #164]
	ldr r2, [r8, #168]
	ldr r3, [r8, #172]
	ldr r4, [r8, #176]
	ldr r5, [r8, #180]
	ldr r6, [r8, #184]
	ldr r7, [r8, #188]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2536]
	str r1, [r8, #2552]
	str r2, [r8, #2568]
	str r3, [r8, #2584]
	str r4, [r8, #2600]
	str r5, [r8, #2616]
	str r6, [r8, #2632]
	str r7, [r8, #2648]
	ldr r0, [r8, #192]
	ldr r1, [r8, #196]
	ldr r2, [r8, #200]
	ldr r3, [r8, #204]
	ldr r4, [r8, #208]
	ldr r5, [r8, #212]
	ldr r6, [r8, #216]
	ldr r7, [r8, #220]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2540]
	str r1, [r8, #2556]
	str r2, [r8, #2572]
	str r3, [r8, #2588]
	str r4, [r8, #2604]
	str r5, [r8, #2620]
	str r6, [r8, #2636]
	str r7, [r8, #2652]
	ldr r1, [r8, #2508]
	ldr r2, [r8, #2512]
	ldr lr, [r8, #2468]
	lsr r10, r2, #3
	cmp r10, #0
	bne 213f
	mov r3, r2
	b 214f
213:
	mov r3, #8
214:
	add r0, r8, #2528
	mov r12, r1
215:
	ldr r10, [r0, #0]
	str r10, [r12, #0]
	ldr r10, [r0, #4]
	str r10, [r12, #4]
	ldr r10, [r0, #8]
	str r10, [r12, #8]
	ldr r10, [r0, #12]
	str r10, [r12, #12]
	add r0, r0, #16
	add r12, r12, #16
	subs r3, r3, #1
	bne 215b
	lsr r10, r2, #3
	cmp r10, #0
	bne 216f
	mov r3, r2
	b 217f
216:
	mov r3, #8
217:
	add r1, r1, #128
	subs r2, r2, r3
	bne 25b
	b 24f
23:
24:
	mov r12, r8
	ldr r4, [r12, #2472]
	ldr r5, [r12, #2476]
	ldr r6, [r12, #2480]
	ldr r7, [r12, #2484]
	ldr r8, [r12, #2488]
	ldr r9, [r12, #2492]
	ldr r10, [r12, #2496]
	ldr r11, [r12, #2500]
	ldr lr, [r12, #2504]
	add r12, sp, #8
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	str r2, [r12, #32]
	str r2, [r12, #36]
	str r2, [r12, #40]
	str r2, [r12, #44]
	str r2, [r12, #48]
	str r2, [r12, #52]
	str r2, [r12, #56]
	str r2, [r12, #60]
	str r2, [r12, #64]
	str r2, [r12, #68]
	str r2, [r12, #72]
	str r2, [r12, #76]
	str r2, [r12, #80]
	str r2, [r12, #84]
	str r2, [r12, #88]
	str r2, [r12, #92]
	str r2, [r12, #96]
	str r2, [r12, #100]
	str r2, [r12, #104]
	str r2, [r12, #108]
	str r2, [r12, #112]
	str r2, [r12, #116]
	str r2, [r12, #120]
	str r2, [r12, #124]
	str r2, [r12, #128]
	str r2, [r12, #132]
	str r2, [r12, #136]
	str r2, [r12, #140]
	str r2, [r12, #144]
	str r2, [r12, #148]
	str r2, [r12, #152]
	str r2, [r12, #156]
	str r2, [r12, #160]
	str r2, [r12, #164]
	str r2, [r12, #168]
	str r2, [r12, #172]
	str r2, [r12, #176]
	str r2, [r12, #180]
	str r2, [r12, #184]
	str r2, [r12, #188]
	str r2, [r12, #192]
	str r2, [r12, #196]
	str r2, [r12, #200]
	str r2, [r12, #204]
	str r2, [r12, #208]
	str r2, [r12, #212]
	str r2, [r12, #216]
	str r2, [r12, #220]
	str r2, [r12, #224]
	str r2, [r12, #228]
	str r2, [r12, #232]
	str r2, [r12, #236]
	str r2, [r12, #240]
	str r2, [r12, #244]
	str r2, [r12, #248]
	str r2, [r12, #252]
	str r2, [r12, #256]
	str r2, [r12, #260]
	str r2, [r12, #264]
	str r2, [r12, #268]
	str r2, [r12, #272]
	str r2, [r12, #276]
	str r2, [r12, #280]
	str r2, [r12, #284]
	str r2, [r12, #288]
	str r2, [r12, #292]
	str r2, [r12, #296]
	str r2, [r12, #300]
	str r2, [r12, #304]
	str r2, [r12, #308]
	str r2, [r12, #312]
	str r2, [r12, #316]
	str r2, [r12, #320]
	str r2, [r12, #324]
	str r2, [r12, #328]
	str r2, [r12, #332]
	str r2, [r12, #336]
	str r2, [r12, #340]
	str r2, [r12, #344]
	str r2, [r12, #348]
	str r2, [r12, #352]
	str r2, [r12, #356]
	str r2, [r12, #360]
	str r2, [r12, #364]
	str r2, [r12, #368]
	str r2, [r12, #372]
	str r2, [r12, #376]
	str r2, [r12, #380]
	str r2, [r12, #384]
	str r2, [r12, #388]
	str r2, [r12, #392]
	str r2, [r12, #396]
	str r2, [r12, #400]
	str r2, [r12, #404]
	str r2, [r12, #408]
	str r2, [r12, #412]
	str r2, [r12, #416]
	str r2, [r12, #420]
	str r2, [r12, #424]
	str r2, [r12, #428]
	str r2, [r12, #432]
	str r2, [r12, #436]
	str r2, [r12, #440]
	str r2, [r12, #444]
	str r2, [r12, #448]
	str r2, [r12, #452]
	str r2, [r12, #456]
	str r2, [r12, #460]
	str r2, [r12, #464]
	str r2, [r12, #468]
	str r2, [r12, #472]
	str r2, [r12, #476]
	str r2, [r12, #480]
	str r2, [r12, #484]
	str r2, [r12, #488]
	str r2, [r12, #492]
	str r2, [r12, #496]
	str r2, [r12, #500]
	str r2, [r12, #504]
	str r2, [r12, #508]
	str r2, [r12, #512]
	str r2, [r12, #516]
	str r2, [r12, #520]
	str r2, [r12, #524]
	str r2, [r12, #528]
	str r2, [r12, #532]
	str r2, [r12, #536]
	str r2, [r12, #540]
	str r2, [r12, #544]
	str r2, [r12, #548]
	str r2, [r12, #552]
	str r2, [r12, #556]
	str r2, [r12, #560]
	str r2, [r12, #564]
	str r2, [r12, #568]
	str r2, [r12, #572]
	str r2, [r12, #576]
	str r2, [r12, #580]
	str r2, [r12, #584]
	str r2, [r12, #588]
	str r2, [r12, #592]
	str r2, [r12, #596]
	str r2, [r12, #600]
	str r2, [r12, #604]
	str r2, [r12, #608]
	str r2, [r12, #612]
	str r2, [r12, #616]
	str r2, [r12, #620]
	str r2, [r12, #624]
	str r2, [r12, #628]
	str r2, [r12, #632]
	str r2, [r12, #636]
	str r2, [r12, #640]
	str r2, [r12, #644]
	str r2, [r12, #648]
	str r2, [r12, #652]
	str r2, [r12, #656]
	str r2, [r12, #660]
	str r2, [r12, #664]
	str r2, [r12, #668]
	str r2, [r12, #672]
	str r2, [r12, #676]
	str r2, [r12, #680]
	str r2, [r12, #684]
	str r2, [r12, #688]
	str r2, [r12, #692]
	str r2, [r12, #696]
	str r2, [r12, #700]
	str r2, [r12, #704]
	str r2, [r12, #708]
	str r2, [r12, #712]
	str r2, [r12, #716]
	str r2, [r12, #720]
	str r2, [r12, #724]
	str r2, [r12, #728]
	str r2, [r12, #732]
	str r2, [r12, #736]
	str r2, [r12, #740]
	str r2, [r12, #744]
	str r2, [r12, #748]
	str r2, [r12, #752]
	str r2, [r12, #756]
	str r2, [r12, #760]
	str r2, [r12, #764]
	str r2, [r12, #768]
	str r2, [r12, #772]
	str r2, [r12, #776]
	str r2, [r12, #780]
	str r2, [r12, #784]
	str r2, [r12, #788]
	str r2, [r12, #792]
	str r2, [r12, #796]
	str r2, [r12, #800]
	str r2, [r12, #804]
	str r2, [r12, #808]
	str r2, [r12, #812]
	str r2, [r12, #816]
	str r2, [r12, #820]
	str r2, [r12, #824]
	str r2, [r12, #828]
	str r2, [r12, #832]
	str r2, [r12, #836]
	str r2, [r12, #840]
	str r2, [r12, #844]
	str r2, [r12, #848]
	str r2, [r12, #852]
	str r2, [r12, #856]
	str r2, [r12, #860]
	str r2, [r12, #864]
	str r2, [r12, #868]
	str r2, [r12, #872]
	str r2, [r12, #876]
	str r2, [r12, #880]
	str r2, [r12, #884]
	str r2, [r12, #888]
	str r2, [r12, #892]
	str r2, [r12, #896]
	str r2, [r12, #900]
	str r2, [r12, #904]
	str r2, [r12, #908]
	str r2, [r12, #912]
	str r2, [r12, #916]
	str r2, [r12, #920]
	str r2, [r12, #924]
	str r2, [r12, #928]
	str r2, [r12, #932]
	str r2, [r12, #936]
	str r2, [r12, #940]
	str r2, [r12, #944]
	str r2, [r12, #948]
	str r2, [r12, #952]
	str r2, [r12, #956]
	str r2, [r12, #960]
	str r2, [r12, #964]
	str r2, [r12, #968]
	str r2, [r12, #972]
	str r2, [r12, #976]
	str r2, [r12, #980]
	str r2, [r12, #984]
	str r2, [r12, #988]
	str r2, [r12, #992]
	str r2, [r12, #996]
	str r2, [r12, #1000]
	str r2, [r12, #1004]
	str r2, [r12, #1008]
	str r2, [r12, #1012]
	str r2, [r12, #1016]
	str r2, [r12, #1020]
	str r2, [r12, #1024]
	str r2, [r12, #1028]
	str r2, [r12, #1032]
	str r2, [r12, #1036]
	str r2, [r12, #1040]
	str r2, [r12, #1044]
	str r2, [r12, #1048]
	str r2, [r12, #1052]
	str r2, [r12, #1056]
	str r2, [r12, #1060]
	str r2, [r12, #1064]
	str r2, [r12, #1068]
	str r2, [r12, #1072]
	str r2, [r12, #1076]
	str r2, [r12, #1080]
	str r2, [r12, #1084]
	str r2, [r12, #1088]
	str r2, [r12, #1092]
	str r2, [r12, #1096]
	str r2, [r12, #1100]
	str r2, [r12, #1104]
	str r2, [r12, #1108]
	str r2, [r12, #1112]
	str r2, [r12, #1116]
	str r2, [r12, #1120]
	str r2, [r12, #1124]
	str r2, [r12, #1128]
	str r2, [r12, #1132]
	str r2, [r12, #1136]
	str r2, [r12, #1140]
	str r2, [r12, #1144]
	str r2, [r12, #1148]
	str r2, [r12, #1152]
	str r2, [r12, #1156]
	str r2, [r12, #1160]
	str r2, [r12, #1164]
	str r2, [r12, #1168]
	str r2, [r12, #1172]
	str r2, [r12, #1176]
	str r2, [r12, #1180]
	str r2, [r12, #1184]
	str r2, [r12, #1188]
	str r2, [r12, #1192]
	str r2, [r12, #1196]
	str r2, [r12, #1200]
	str r2, [r12, #1204]
	str r2, [r12, #1208]
	str r2, [r12, #1212]
	str r2, [r12, #1216]
	str r2, [r12, #1220]
	str r2, [r12, #1224]
	str r2, [r12, #1228]
	str r2, [r12, #1232]
	str r2, [r12, #1236]
	str r2, [r12, #1240]
	str r2, [r12, #1244]
	str r2, [r12, #1248]
	str r2, [r12, #1252]
	str r2, [r12, #1256]
	str r2, [r12, #1260]
	str r2, [r12, #1264]
	str r2, [r12, #1268]
	str r2, [r12, #1272]
	str r2, [r12, #1276]
	str r2, [r12, #1280]
	str r2, [r12, #1284]
	str r2, [r12, #1288]
	str r2, [r12, #1292]
	str r2, [r12, #1296]
	str r2, [r12, #1300]
	str r2, [r12, #1304]
	str r2, [r12, #1308]
	str r2, [r12, #1312]
	str r2, [r12, #1316]
	str r2, [r12, #1320]
	str r2, [r12, #1324]
	str r2, [r12, #1328]
	str r2, [r12, #1332]
	str r2, [r12, #1336]
	str r2, [r12, #1340]
	str r2, [r12, #1344]
	str r2, [r12, #1348]
	str r2, [r12, #1352]
	str r2, [r12, #1356]
	str r2, [r12, #1360]
	str r2, [r12, #1364]
	str r2, [r12, #1368]
	str r2, [r12, #1372]
	str r2, [r12, #1376]
	str r2, [r12, #1380]
	str r2, [r12, #1384]
	str r2, [r12, #1388]
	str r2, [r12, #1392]
	str r2, [r12, #1396]
	str r2, [r12, #1400]
	str r2, [r12, #1404]
	str r2, [r12, #1408]
	str r2, [r12, #1412]
	str r2, [r12, #1416]
	str r2, [r12, #1420]
	str r2, [r12, #1424]
	str r2, [r12, #1428]
	str r2, [r12, #1432]
	str r2, [r12, #1436]
	str r2, [r12, #1440]
	str r2, [r12, #1444]
	str r2, [r12, #1448]
	str r2, [r12, #1452]
	str r2, [r12, #1456]
	str r2, [r12, #1460]
	str r2, [r12, #1464]
	str r2, [r12, #1468]
	str r2, [r12, #1472]
	str r2, [r12, #1476]
	str r2, [r12, #1480]
	str r2, [r12, #1484]
	str r2, [r12, #1488]
	str r2, [r12, #1492]
	str r2, [r12, #1496]
	str r2, [r12, #1500]
	str r2, [r12, #1504]
	str r2, [r12, #1508]
	str r2, [r12, #1512]
	str r2, [r12, #1516]
	str r2, [r12, #1520]
	str r2, [r12, #1524]
	str r2, [r12, #1528]
	str r2, [r12, #1532]
	str r2, [r12, #1536]
	str r2, [r12, #1540]
	str r2, [r12, #1544]
	str r2, [r12, #1548]
	str r2, [r12, #1552]
	str r2, [r12, #1556]
	str r2, [r12, #1560]
	str r2, [r12, #1564]
	str r2, [r12, #1568]
	str r2, [r12, #1572]
	str r2, [r12, #1576]
	str r2, [r12, #1580]
	str r2, [r12, #1584]
	str r2, [r12, #1588]
	str r2, [r12, #1592]
	str r2, [r12, #1596]
	str r2, [r12, #1600]
	str r2, [r12, #1604]
	str r2, [r12, #1608]
	str r2, [r12, #1612]
	str r2, [r12, #1616]
	str r2, [r12, #1620]
	str r2, [r12, #1624]
	str r2, [r12, #1628]
	str r2, [r12, #1632]
	str r2, [r12, #1636]
	str r2, [r12, #1640]
	str r2, [r12, #1644]
	str r2, [r12, #1648]
	str r2, [r12, #1652]
	str r2, [r12, #1656]
	str r2, [r12, #1660]
	str r2, [r12, #1664]
	str r2, [r12, #1668]
	str r2, [r12, #1672]
	str r2, [r12, #1676]
	str r2, [r12, #1680]
	str r2, [r12, #1684]
	str r2, [r12, #1688]
	str r2, [r12, #1692]
	str r2, [r12, #1696]
	str r2, [r12, #1700]
	str r2, [r12, #1704]
	str r2, [r12, #1708]
	str r2, [r12, #1712]
	str r2, [r12, #1716]
	str r2, [r12, #1720]
	str r2, [r12, #1724]
	str r2, [r12, #1728]
	str r2, [r12, #1732]
	str r2, [r12, #1736]
	str r2, [r12, #1740]
	str r2, [r12, #1744]
	str r2, [r12, #1748]
	str r2, [r12, #1752]
	str r2, [r12, #1756]
	str r2, [r12, #1760]
	str r2, [r12, #1764]
	str r2, [r12, #1768]
	str r2, [r12, #1772]
	str r2, [r12, #1776]
	str r2, [r12, #1780]
	str r2, [r12, #1784]
	str r2, [r12, #1788]
	str r2, [r12, #1792]
	str r2, [r12, #1796]
	str r2, [r12, #1800]
	str r2, [r12, #1804]
	str r2, [r12, #1808]
	str r2, [r12, #1812]
	str r2, [r12, #1816]
	str r2, [r12, #1820]
	str r2, [r12, #1824]
	str r2, [r12, #1828]
	str r2, [r12, #1832]
	str r2, [r12, #1836]
	str r2, [r12, #1840]
	str r2, [r12, #1844]
	str r2, [r12, #1848]
	str r2, [r12, #1852]
	str r2, [r12, #1856]
	str r2, [r12, #1860]
	str r2, [r12, #1864]
	str r2, [r12, #1868]
	str r2, [r12, #1872]
	str r2, [r12, #1876]
	str r2, [r12, #1880]
	str r2, [r12, #1884]
	str r2, [r12, #1888]
	str r2, [r12, #1892]
	str r2, [r12, #1896]
	str r2, [r12, #1900]
	str r2, [r12, #1904]
	str r2, [r12, #1908]
	str r2, [r12, #1912]
	str r2, [r12, #1916]
	str r2, [r12, #1920]
	str r2, [r12, #1924]
	str r2, [r12, #1928]
	str r2, [r12, #1932]
	str r2, [r12, #1936]
	str r2, [r12, #1940]
	str r2, [r12, #1944]
	str r2, [r12, #1948]
	str r2, [r12, #1952]
	str r2, [r12, #1956]
	str r2, [r12, #1960]
	str r2, [r12, #1964]
	str r2, [r12, #1968]
	str r2, [r12, #1972]
	str r2, [r12, #1976]
	str r2, [r12, #1980]
	str r2, [r12, #1984]
	str r2, [r12, #1988]
	str r2, [r12, #1992]
	str r2, [r12, #1996]
	str r2, [r12, #2000]
	str r2, [r12, #2004]
	str r2, [r12, #2008]
	str r2, [r12, #2012]
	str r2, [r12, #2016]
	str r2, [r12, #2020]
	str r2, [r12, #2024]
	str r2, [r12, #2028]
	str r2, [r12, #2032]
	str r2, [r12, #2036]
	str r2, [r12, #2040]
	str r2, [r12, #2044]
	str r2, [r12, #2048]
	str r2, [r12, #2052]
	str r2, [r12, #2056]
	str r2, [r12, #2060]
	str r2, [r12, #2064]
	str r2, [r12, #2068]
	str r2, [r12, #2072]
	str r2, [r12, #2076]
	str r2, [r12, #2080]
	str r2, [r12, #2084]
	str r2, [r12, #2088]
	str r2, [r12, #2092]
	str r2, [r12, #2096]
	str r2, [r12, #2100]
	str r2, [r12, #2104]
	str r2, [r12, #2108]
	str r2, [r12, #2112]
	str r2, [r12, #2116]
	str r2, [r12, #2120]
	str r2, [r12, #2124]
	str r2, [r12, #2128]
	str r2, [r12, #2132]
	str r2, [r12, #2136]
	str r2, [r12, #2140]
	str r2, [r12, #2144]
	str r2, [r12, #2148]
	str r2, [r12, #2152]
	str r2, [r12, #2156]
	str r2, [r12, #2160]
	str r2, [r12, #2164]
	str r2, [r12, #2168]
	str r2, [r12, #2172]
	str r2, [r12, #2176]
	str r2, [r12, #2180]
	str r2, [r12, #2184]
	str r2, [r12, #2188]
	str r2, [r12, #2192]
	str r2, [r12, #2196]
	str r2, [r12, #2200]
	str r2, [r12, #2204]
	str r2, [r12, #2208]
	str r2, [r12, #2212]
	str r2, [r12, #2216]
	str r2, [r12, #2220]
	str r2, [r12, #2224]
	str r2, [r12, #2228]
	str r2, [r12, #2232]
	str r2, [r12, #2236]
	str r2, [r12, #2240]
	str r2, [r12, #2244]
	str r2, [r12, #2248]
	str r2, [r12, #2252]
	str r2, [r12, #2256]
	str r2, [r12, #2260]
	str r2, [r12, #2264]
	str r2, [r12, #2268]
	str r2, [r12, #2272]
	str r2, [r12, #2276]
	str r2, [r12, #2280]
	str r2, [r12, #2284]
	str r2, [r12, #2288]
	str r2, [r12, #2292]
	str r2, [r12, #2296]
	str r2, [r12, #2300]
	str r2, [r12, #2304]
	str r2, [r12, #2308]
	str r2, [r12, #2312]
	str r2, [r12, #2316]
	str r2, [r12, #2320]
	str r2, [r12, #2324]
	str r2, [r12, #2328]
	str r2, [r12, #2332]
	str r2, [r12, #2336]
	str r2, [r12, #2340]
	str r2, [r12, #2344]
	str r2, [r12, #2348]
	str r2, [r12, #2352]
	str r2, [r12, #2356]
	str r2, [r12, #2360]
	str r2, [r12, #2364]
	str r2, [r12, #2368]
	str r2, [r12, #2372]
	str r2, [r12, #2376]
	str r2, [r12, #2380]
	str r2, [r12, #2384]
	str r2, [r12, #2388]
	str r2, [r12, #2392]
	str r2, [r12, #2396]
	str r2, [r12, #2400]
	str r2, [r12, #2404]
	str r2, [r12, #2408]
	str r2, [r12, #2412]
	str r2, [r12, #2416]
	str r2, [r12, #2420]
	str r2, [r12, #2424]
	str r2, [r12, #2428]
	str r2, [r12, #2432]
	str r2, [r12, #2436]
	str r2, [r12, #2440]
	str r2, [r12, #2444]
	str r2, [r12, #2448]
	str r2, [r12, #2452]
	str r2, [r12, #2456]
	str r2, [r12, #2460]
	str r2, [r12, #2464]
	str r2, [r12, #2468]
	str r2, [r12, #2472]
	str r2, [r12, #2476]
	str r2, [r12, #2480]
	str r2, [r12, #2484]
	str r2, [r12, #2488]
	str r2, [r12, #2492]
	str r2, [r12, #2496]
	str r2, [r12, #2500]
	str r2, [r12, #2504]
	str r2, [r12, #2508]
	str r2, [r12, #2512]
	str r2, [r12, #2516]
	str r2, [r12, #2520]
	str r2, [r12, #2524]
	str r2, [r12, #2528]
	str r2, [r12, #2532]
	str r2, [r12, #2536]
	str r2, [r12, #2540]
	str r2, [r12, #2544]
	str r2, [r12, #2548]
	str r2, [r12, #2552]
	str r2, [r12, #2556]
	str r2, [r12, #2560]
	str r2, [r12, #2564]
	str r2, [r12, #2568]
	str r2, [r12, #2572]
	str r2, [r12, #2576]
	str r2, [r12, #2580]
	str r2, [r12, #2584]
	str r2, [r12, #2588]
	str r2, [r12, #2592]
	str r2, [r12, #2596]
	str r2, [r12, #2600]
	str r2, [r12, #2604]
	str r2, [r12, #2608]
	str r2, [r12, #2612]
	str r2, [r12, #2616]
	str r2, [r12, #2620]
	str r2, [r12, #2624]
	str r2, [r12, #2628]
	str r2, [r12, #2632]
	str r2, [r12, #2636]
	str r2, [r12, #2640]
	str r2, [r12, #2644]
	str r2, [r12, #2648]
	str r2, [r12, #2652]
	str r2, [r12, #2656]
	str r2, [r12, #2660]
	str r2, [r12, #2664]
	str r2, [r12, #2668]
	str r2, [r12, #2672]
	str r2, [r12, #2676]
	str r2, [r12, #2680]
	str r2, [r12, #2684]
	str r2, [r12, #2688]
	str r2, [r12, #2692]
	str r2, [r12, #2696]
	str r2, [r12, #2700]
	str r2, [r12, #2704]
	str r2, [r12, #2708]
	str r2, [r12, #2712]
	str r2, [r12, #2716]
	add sp, sp, #2816
	bx lr

vg_camellia_ecb_decrypt:
	sub sp, sp, #2816
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
	str r4, [r12, #2472]
	str r5, [r12, #2476]
	str r6, [r12, #2480]
	str r7, [r12, #2484]
	str r8, [r12, #2488]
	str r9, [r12, #2492]
	str r10, [r12, #2496]
	str r11, [r12, #2500]
	str lr, [r12, #2504]
	mov r8, r12
	mov r12, r0
	cmp r1, #18
	mov r1, r2
	mov r2, r3
	beq 20f
	add r12, r12, #256
	mov lr, #30
	b 21f
20:
	add r12, r12, #192
	mov lr, #22
21:
	add r9, r8, #288
	ldr r4, [r12, #0]
	movw r11, #257
	movt r11, #257
	and r5, r11, r4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #0]
	and r5, r11, r4, lsr #1
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #4]
	and r5, r11, r4, lsr #2
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #8]
	and r5, r11, r4, lsr #3
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #12]
	and r5, r11, r4, lsr #4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #16]
	and r5, r11, r4, lsr #5
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #20]
	and r5, r11, r4, lsr #6
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #24]
	and r5, r11, r4, lsr #7
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #28]
	ldr r4, [r12, #4]
	movw r11, #257
	movt r11, #257
	and r5, r11, r4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #32]
	and r5, r11, r4, lsr #1
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #36]
	and r5, r11, r4, lsr #2
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #40]
	and r5, r11, r4, lsr #3
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #44]
	and r5, r11, r4, lsr #4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #48]
	and r5, r11, r4, lsr #5
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #52]
	and r5, r11, r4, lsr #6
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #56]
	and r5, r11, r4, lsr #7
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #60]
	add r9, r9, #64
	ldr r4, [r12, #8]
	movw r11, #257
	movt r11, #257
	and r5, r11, r4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #0]
	and r5, r11, r4, lsr #1
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #4]
	and r5, r11, r4, lsr #2
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #8]
	and r5, r11, r4, lsr #3
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #12]
	and r5, r11, r4, lsr #4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #16]
	and r5, r11, r4, lsr #5
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #20]
	and r5, r11, r4, lsr #6
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #24]
	and r5, r11, r4, lsr #7
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #28]
	ldr r4, [r12, #12]
	movw r11, #257
	movt r11, #257
	and r5, r11, r4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #32]
	and r5, r11, r4, lsr #1
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #36]
	and r5, r11, r4, lsr #2
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #40]
	and r5, r11, r4, lsr #3
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #44]
	and r5, r11, r4, lsr #4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #48]
	and r5, r11, r4, lsr #5
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #52]
	and r5, r11, r4, lsr #6
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #56]
	and r5, r11, r4, lsr #7
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #60]
	add r9, r9, #64
	sub r12, r12, #8
22:
	ldr r4, [r12, #0]
	movw r11, #257
	movt r11, #257
	and r5, r11, r4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #0]
	and r5, r11, r4, lsr #1
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #4]
	and r5, r11, r4, lsr #2
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #8]
	and r5, r11, r4, lsr #3
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #12]
	and r5, r11, r4, lsr #4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #16]
	and r5, r11, r4, lsr #5
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #20]
	and r5, r11, r4, lsr #6
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #24]
	and r5, r11, r4, lsr #7
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #28]
	ldr r4, [r12, #4]
	movw r11, #257
	movt r11, #257
	and r5, r11, r4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #32]
	and r5, r11, r4, lsr #1
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #36]
	and r5, r11, r4, lsr #2
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #40]
	and r5, r11, r4, lsr #3
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #44]
	and r5, r11, r4, lsr #4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #48]
	and r5, r11, r4, lsr #5
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #52]
	and r5, r11, r4, lsr #6
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #56]
	and r5, r11, r4, lsr #7
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #60]
	add r9, r9, #64
	sub r12, r12, #8
	subs lr, lr, #1
	bne 22b
	sub r12, r12, #8
	ldr r4, [r12, #0]
	movw r11, #257
	movt r11, #257
	and r5, r11, r4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #0]
	and r5, r11, r4, lsr #1
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #4]
	and r5, r11, r4, lsr #2
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #8]
	and r5, r11, r4, lsr #3
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #12]
	and r5, r11, r4, lsr #4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #16]
	and r5, r11, r4, lsr #5
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #20]
	and r5, r11, r4, lsr #6
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #24]
	and r5, r11, r4, lsr #7
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #28]
	ldr r4, [r12, #4]
	movw r11, #257
	movt r11, #257
	and r5, r11, r4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #32]
	and r5, r11, r4, lsr #1
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #36]
	and r5, r11, r4, lsr #2
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #40]
	and r5, r11, r4, lsr #3
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #44]
	and r5, r11, r4, lsr #4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #48]
	and r5, r11, r4, lsr #5
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #52]
	and r5, r11, r4, lsr #6
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #56]
	and r5, r11, r4, lsr #7
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #60]
	add r9, r9, #64
	ldr r4, [r12, #8]
	movw r11, #257
	movt r11, #257
	and r5, r11, r4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #0]
	and r5, r11, r4, lsr #1
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #4]
	and r5, r11, r4, lsr #2
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #8]
	and r5, r11, r4, lsr #3
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #12]
	and r5, r11, r4, lsr #4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #16]
	and r5, r11, r4, lsr #5
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #20]
	and r5, r11, r4, lsr #6
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #24]
	and r5, r11, r4, lsr #7
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #28]
	ldr r4, [r12, #12]
	movw r11, #257
	movt r11, #257
	and r5, r11, r4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #32]
	and r5, r11, r4, lsr #1
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #36]
	and r5, r11, r4, lsr #2
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #40]
	and r5, r11, r4, lsr #3
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #44]
	and r5, r11, r4, lsr #4
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #48]
	and r5, r11, r4, lsr #5
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #52]
	and r5, r11, r4, lsr #6
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #56]
	and r5, r11, r4, lsr #7
	eor r5, r5, r5, ror #31
	eor r5, r5, r5, ror #30
	eor r5, r5, r5, ror #28
	str r5, [r9, #60]
	add r9, r9, #64
	sub lr, r9, #128
	cmp r2, #0
	beq 23f
25:
	lsr r10, r2, #3
	cmp r10, #0
	bne 26f
	mov r3, r2
	b 27f
26:
	mov r3, #8
27:
	mov r0, r1
	add r12, r8, #2528
28:
	ldr r10, [r0, #0]
	str r10, [r12, #0]
	ldr r10, [r0, #4]
	str r10, [r12, #4]
	ldr r10, [r0, #8]
	str r10, [r12, #8]
	ldr r10, [r0, #12]
	str r10, [r12, #12]
	add r0, r0, #16
	add r12, r12, #16
	subs r3, r3, #1
	bne 28b
	str r1, [r8, #2508]
	str r2, [r8, #2512]
	str lr, [r8, #2468]
	add r12, r8, #2528
	ldr r0, [r12, #0]
	ldr r1, [r12, #16]
	ldr r2, [r12, #32]
	ldr r3, [r12, #48]
	ldr r4, [r12, #64]
	ldr r5, [r12, #80]
	ldr r6, [r12, #96]
	ldr r7, [r12, #112]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #160]
	str r1, [r8, #164]
	str r2, [r8, #168]
	str r3, [r8, #172]
	str r4, [r8, #176]
	str r5, [r8, #180]
	str r6, [r8, #184]
	str r7, [r8, #188]
	ldr r0, [r12, #4]
	ldr r1, [r12, #20]
	ldr r2, [r12, #36]
	ldr r3, [r12, #52]
	ldr r4, [r12, #68]
	ldr r5, [r12, #84]
	ldr r6, [r12, #100]
	ldr r7, [r12, #116]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #192]
	str r1, [r8, #196]
	str r2, [r8, #200]
	str r3, [r8, #204]
	str r4, [r8, #208]
	str r5, [r8, #212]
	str r6, [r8, #216]
	str r7, [r8, #220]
	ldr r0, [r12, #8]
	ldr r1, [r12, #24]
	ldr r2, [r12, #40]
	ldr r3, [r12, #56]
	ldr r4, [r12, #72]
	ldr r5, [r12, #88]
	ldr r6, [r12, #104]
	ldr r7, [r12, #120]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #224]
	str r1, [r8, #228]
	str r2, [r8, #232]
	str r3, [r8, #236]
	str r4, [r8, #240]
	str r5, [r8, #244]
	str r6, [r8, #248]
	str r7, [r8, #252]
	ldr r0, [r12, #12]
	ldr r1, [r12, #28]
	ldr r2, [r12, #44]
	ldr r3, [r12, #60]
	ldr r4, [r12, #76]
	ldr r5, [r12, #92]
	ldr r6, [r12, #108]
	ldr r7, [r12, #124]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #256]
	str r1, [r8, #260]
	str r2, [r8, #264]
	str r3, [r8, #268]
	str r4, [r8, #272]
	str r5, [r8, #276]
	str r6, [r8, #280]
	str r7, [r8, #284]
	add r9, r8, #288
	ldr r11, [r8, #160]
	ldr r10, [r9, #0]
	eor r11, r11, r10
	str r11, [r8, #160]
	ldr r11, [r8, #164]
	ldr r10, [r9, #4]
	eor r11, r11, r10
	str r11, [r8, #164]
	ldr r11, [r8, #168]
	ldr r10, [r9, #8]
	eor r11, r11, r10
	str r11, [r8, #168]
	ldr r11, [r8, #172]
	ldr r10, [r9, #12]
	eor r11, r11, r10
	str r11, [r8, #172]
	ldr r11, [r8, #176]
	ldr r10, [r9, #16]
	eor r11, r11, r10
	str r11, [r8, #176]
	ldr r11, [r8, #180]
	ldr r10, [r9, #20]
	eor r11, r11, r10
	str r11, [r8, #180]
	ldr r11, [r8, #184]
	ldr r10, [r9, #24]
	eor r11, r11, r10
	str r11, [r8, #184]
	ldr r11, [r8, #188]
	ldr r10, [r9, #28]
	eor r11, r11, r10
	str r11, [r8, #188]
	ldr r11, [r8, #192]
	ldr r10, [r9, #32]
	eor r11, r11, r10
	str r11, [r8, #192]
	ldr r11, [r8, #196]
	ldr r10, [r9, #36]
	eor r11, r11, r10
	str r11, [r8, #196]
	ldr r11, [r8, #200]
	ldr r10, [r9, #40]
	eor r11, r11, r10
	str r11, [r8, #200]
	ldr r11, [r8, #204]
	ldr r10, [r9, #44]
	eor r11, r11, r10
	str r11, [r8, #204]
	ldr r11, [r8, #208]
	ldr r10, [r9, #48]
	eor r11, r11, r10
	str r11, [r8, #208]
	ldr r11, [r8, #212]
	ldr r10, [r9, #52]
	eor r11, r11, r10
	str r11, [r8, #212]
	ldr r11, [r8, #216]
	ldr r10, [r9, #56]
	eor r11, r11, r10
	str r11, [r8, #216]
	ldr r11, [r8, #220]
	ldr r10, [r9, #60]
	eor r11, r11, r10
	str r11, [r8, #220]
	ldr r11, [r8, #224]
	ldr r10, [r9, #64]
	eor r11, r11, r10
	str r11, [r8, #224]
	ldr r11, [r8, #228]
	ldr r10, [r9, #68]
	eor r11, r11, r10
	str r11, [r8, #228]
	ldr r11, [r8, #232]
	ldr r10, [r9, #72]
	eor r11, r11, r10
	str r11, [r8, #232]
	ldr r11, [r8, #236]
	ldr r10, [r9, #76]
	eor r11, r11, r10
	str r11, [r8, #236]
	ldr r11, [r8, #240]
	ldr r10, [r9, #80]
	eor r11, r11, r10
	str r11, [r8, #240]
	ldr r11, [r8, #244]
	ldr r10, [r9, #84]
	eor r11, r11, r10
	str r11, [r8, #244]
	ldr r11, [r8, #248]
	ldr r10, [r9, #88]
	eor r11, r11, r10
	str r11, [r8, #248]
	ldr r11, [r8, #252]
	ldr r10, [r9, #92]
	eor r11, r11, r10
	str r11, [r8, #252]
	ldr r11, [r8, #256]
	ldr r10, [r9, #96]
	eor r11, r11, r10
	str r11, [r8, #256]
	ldr r11, [r8, #260]
	ldr r10, [r9, #100]
	eor r11, r11, r10
	str r11, [r8, #260]
	ldr r11, [r8, #264]
	ldr r10, [r9, #104]
	eor r11, r11, r10
	str r11, [r8, #264]
	ldr r11, [r8, #268]
	ldr r10, [r9, #108]
	eor r11, r11, r10
	str r11, [r8, #268]
	ldr r11, [r8, #272]
	ldr r10, [r9, #112]
	eor r11, r11, r10
	str r11, [r8, #272]
	ldr r11, [r8, #276]
	ldr r10, [r9, #116]
	eor r11, r11, r10
	str r11, [r8, #276]
	ldr r11, [r8, #280]
	ldr r10, [r9, #120]
	eor r11, r11, r10
	str r11, [r8, #280]
	ldr r11, [r8, #284]
	ldr r10, [r9, #124]
	eor r11, r11, r10
	str r11, [r8, #284]
	add r9, r9, #128
29:
	add r10, r9, #384
	str r10, [r8, #2464]
210:
	ldr r0, [r8, #160]
	ldr r10, [r9, #0]
	eor r0, r0, r10
	ldr r1, [r8, #164]
	ldr r10, [r9, #4]
	eor r1, r1, r10
	ldr r2, [r8, #168]
	ldr r10, [r9, #8]
	eor r2, r2, r10
	ldr r3, [r8, #172]
	ldr r10, [r9, #12]
	eor r3, r3, r10
	ldr r4, [r8, #176]
	ldr r10, [r9, #16]
	eor r4, r4, r10
	ldr r5, [r8, #180]
	ldr r10, [r9, #20]
	eor r5, r5, r10
	ldr r6, [r8, #184]
	ldr r10, [r9, #24]
	eor r6, r6, r10
	ldr r7, [r8, #188]
	ldr r10, [r9, #28]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #4278190080
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #4278190080
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #4278190080
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #4278190080
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #4278190080
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #4278190080
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #4278190080
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #4278190080
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #65280
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #65280
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #16711680
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #16711680
	eor r7, r7, r10
	str r0, [r8, #128]
	str r1, [r8, #132]
	str r2, [r8, #136]
	str r3, [r8, #140]
	str r4, [r8, #144]
	str r5, [r8, #148]
	str r6, [r8, #152]
	str r7, [r8, #156]
	ldr r0, [r8, #192]
	ldr r10, [r9, #32]
	eor r0, r0, r10
	ldr r1, [r8, #196]
	ldr r10, [r9, #36]
	eor r1, r1, r10
	ldr r2, [r8, #200]
	ldr r10, [r9, #40]
	eor r2, r2, r10
	ldr r3, [r8, #204]
	ldr r10, [r9, #44]
	eor r3, r3, r10
	ldr r4, [r8, #208]
	ldr r10, [r9, #48]
	eor r4, r4, r10
	ldr r5, [r8, #212]
	ldr r10, [r9, #52]
	eor r5, r5, r10
	ldr r6, [r8, #216]
	ldr r10, [r9, #56]
	eor r6, r6, r10
	ldr r7, [r8, #220]
	ldr r10, [r9, #60]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #16711680
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #16711680
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #255
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #255
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #255
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #255
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #255
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #255
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #255
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #255
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #65280
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #65280
	eor r7, r7, r10
	ldr r11, [r8, #128]
	eor r11, r11, r0
	eor r11, r11, r0, ror #16
	eor r0, r0, r11
	eor r0, r0, r11, ror #8
	eor r11, r11, r0, ror #16
	ldr r10, [r8, #224]
	eor r10, r10, r11
	str r10, [r8, #224]
	ldr r10, [r8, #256]
	eor r10, r10, r0
	str r10, [r8, #256]
	ldr r11, [r8, #132]
	eor r11, r11, r1
	eor r11, r11, r1, ror #16
	eor r1, r1, r11
	eor r1, r1, r11, ror #8
	eor r11, r11, r1, ror #16
	ldr r10, [r8, #228]
	eor r10, r10, r11
	str r10, [r8, #228]
	ldr r10, [r8, #260]
	eor r10, r10, r1
	str r10, [r8, #260]
	ldr r11, [r8, #136]
	eor r11, r11, r2
	eor r11, r11, r2, ror #16
	eor r2, r2, r11
	eor r2, r2, r11, ror #8
	eor r11, r11, r2, ror #16
	ldr r10, [r8, #232]
	eor r10, r10, r11
	str r10, [r8, #232]
	ldr r10, [r8, #264]
	eor r10, r10, r2
	str r10, [r8, #264]
	ldr r11, [r8, #140]
	eor r11, r11, r3
	eor r11, r11, r3, ror #16
	eor r3, r3, r11
	eor r3, r3, r11, ror #8
	eor r11, r11, r3, ror #16
	ldr r10, [r8, #236]
	eor r10, r10, r11
	str r10, [r8, #236]
	ldr r10, [r8, #268]
	eor r10, r10, r3
	str r10, [r8, #268]
	ldr r11, [r8, #144]
	eor r11, r11, r4
	eor r11, r11, r4, ror #16
	eor r4, r4, r11
	eor r4, r4, r11, ror #8
	eor r11, r11, r4, ror #16
	ldr r10, [r8, #240]
	eor r10, r10, r11
	str r10, [r8, #240]
	ldr r10, [r8, #272]
	eor r10, r10, r4
	str r10, [r8, #272]
	ldr r11, [r8, #148]
	eor r11, r11, r5
	eor r11, r11, r5, ror #16
	eor r5, r5, r11
	eor r5, r5, r11, ror #8
	eor r11, r11, r5, ror #16
	ldr r10, [r8, #244]
	eor r10, r10, r11
	str r10, [r8, #244]
	ldr r10, [r8, #276]
	eor r10, r10, r5
	str r10, [r8, #276]
	ldr r11, [r8, #152]
	eor r11, r11, r6
	eor r11, r11, r6, ror #16
	eor r6, r6, r11
	eor r6, r6, r11, ror #8
	eor r11, r11, r6, ror #16
	ldr r10, [r8, #248]
	eor r10, r10, r11
	str r10, [r8, #248]
	ldr r10, [r8, #280]
	eor r10, r10, r6
	str r10, [r8, #280]
	ldr r11, [r8, #156]
	eor r11, r11, r7
	eor r11, r11, r7, ror #16
	eor r7, r7, r11
	eor r7, r7, r11, ror #8
	eor r11, r11, r7, ror #16
	ldr r10, [r8, #252]
	eor r10, r10, r11
	str r10, [r8, #252]
	ldr r10, [r8, #284]
	eor r10, r10, r7
	str r10, [r8, #284]
	ldr r0, [r8, #224]
	ldr r10, [r9, #64]
	eor r0, r0, r10
	ldr r1, [r8, #228]
	ldr r10, [r9, #68]
	eor r1, r1, r10
	ldr r2, [r8, #232]
	ldr r10, [r9, #72]
	eor r2, r2, r10
	ldr r3, [r8, #236]
	ldr r10, [r9, #76]
	eor r3, r3, r10
	ldr r4, [r8, #240]
	ldr r10, [r9, #80]
	eor r4, r4, r10
	ldr r5, [r8, #244]
	ldr r10, [r9, #84]
	eor r5, r5, r10
	ldr r6, [r8, #248]
	ldr r10, [r9, #88]
	eor r6, r6, r10
	ldr r7, [r8, #252]
	ldr r10, [r9, #92]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #4278190080
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #4278190080
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #4278190080
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #4278190080
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #4278190080
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #4278190080
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #4278190080
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #4278190080
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #65280
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #65280
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #16711680
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #16711680
	eor r7, r7, r10
	str r0, [r8, #128]
	str r1, [r8, #132]
	str r2, [r8, #136]
	str r3, [r8, #140]
	str r4, [r8, #144]
	str r5, [r8, #148]
	str r6, [r8, #152]
	str r7, [r8, #156]
	ldr r0, [r8, #256]
	ldr r10, [r9, #96]
	eor r0, r0, r10
	ldr r1, [r8, #260]
	ldr r10, [r9, #100]
	eor r1, r1, r10
	ldr r2, [r8, #264]
	ldr r10, [r9, #104]
	eor r2, r2, r10
	ldr r3, [r8, #268]
	ldr r10, [r9, #108]
	eor r3, r3, r10
	ldr r4, [r8, #272]
	ldr r10, [r9, #112]
	eor r4, r4, r10
	ldr r5, [r8, #276]
	ldr r10, [r9, #116]
	eor r5, r5, r10
	ldr r6, [r8, #280]
	ldr r10, [r9, #120]
	eor r6, r6, r10
	ldr r7, [r8, #284]
	ldr r10, [r9, #124]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #16711680
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #16711680
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #255
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #255
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #255
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #255
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #255
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #255
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #255
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #255
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #65280
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #65280
	eor r7, r7, r10
	ldr r11, [r8, #128]
	eor r11, r11, r0
	eor r11, r11, r0, ror #16
	eor r0, r0, r11
	eor r0, r0, r11, ror #8
	eor r11, r11, r0, ror #16
	ldr r10, [r8, #160]
	eor r10, r10, r11
	str r10, [r8, #160]
	ldr r10, [r8, #192]
	eor r10, r10, r0
	str r10, [r8, #192]
	ldr r11, [r8, #132]
	eor r11, r11, r1
	eor r11, r11, r1, ror #16
	eor r1, r1, r11
	eor r1, r1, r11, ror #8
	eor r11, r11, r1, ror #16
	ldr r10, [r8, #164]
	eor r10, r10, r11
	str r10, [r8, #164]
	ldr r10, [r8, #196]
	eor r10, r10, r1
	str r10, [r8, #196]
	ldr r11, [r8, #136]
	eor r11, r11, r2
	eor r11, r11, r2, ror #16
	eor r2, r2, r11
	eor r2, r2, r11, ror #8
	eor r11, r11, r2, ror #16
	ldr r10, [r8, #168]
	eor r10, r10, r11
	str r10, [r8, #168]
	ldr r10, [r8, #200]
	eor r10, r10, r2
	str r10, [r8, #200]
	ldr r11, [r8, #140]
	eor r11, r11, r3
	eor r11, r11, r3, ror #16
	eor r3, r3, r11
	eor r3, r3, r11, ror #8
	eor r11, r11, r3, ror #16
	ldr r10, [r8, #172]
	eor r10, r10, r11
	str r10, [r8, #172]
	ldr r10, [r8, #204]
	eor r10, r10, r3
	str r10, [r8, #204]
	ldr r11, [r8, #144]
	eor r11, r11, r4
	eor r11, r11, r4, ror #16
	eor r4, r4, r11
	eor r4, r4, r11, ror #8
	eor r11, r11, r4, ror #16
	ldr r10, [r8, #176]
	eor r10, r10, r11
	str r10, [r8, #176]
	ldr r10, [r8, #208]
	eor r10, r10, r4
	str r10, [r8, #208]
	ldr r11, [r8, #148]
	eor r11, r11, r5
	eor r11, r11, r5, ror #16
	eor r5, r5, r11
	eor r5, r5, r11, ror #8
	eor r11, r11, r5, ror #16
	ldr r10, [r8, #180]
	eor r10, r10, r11
	str r10, [r8, #180]
	ldr r10, [r8, #212]
	eor r10, r10, r5
	str r10, [r8, #212]
	ldr r11, [r8, #152]
	eor r11, r11, r6
	eor r11, r11, r6, ror #16
	eor r6, r6, r11
	eor r6, r6, r11, ror #8
	eor r11, r11, r6, ror #16
	ldr r10, [r8, #184]
	eor r10, r10, r11
	str r10, [r8, #184]
	ldr r10, [r8, #216]
	eor r10, r10, r6
	str r10, [r8, #216]
	ldr r11, [r8, #156]
	eor r11, r11, r7
	eor r11, r11, r7, ror #16
	eor r7, r7, r11
	eor r7, r7, r11, ror #8
	eor r11, r11, r7, ror #16
	ldr r10, [r8, #188]
	eor r10, r10, r11
	str r10, [r8, #188]
	ldr r10, [r8, #220]
	eor r10, r10, r7
	str r10, [r8, #220]
	add r9, r9, #128
	ldr r10, [r8, #2464]
	cmp r9, r10
	bne 210b
	ldr r10, [r8, #2468]
	cmp r9, r10
	bne 211f
	b 212f
211:
	ldr r0, [r8, #224]
	ldr r1, [r8, #228]
	ldr r2, [r8, #232]
	ldr r3, [r8, #236]
	ldr r4, [r8, #240]
	ldr r5, [r8, #244]
	ldr r6, [r8, #248]
	ldr r7, [r8, #252]
	ldr r10, [r9, #96]
	ldr r11, [r8, #256]
	orr r10, r10, r11
	eor r0, r0, r10
	ldr r10, [r9, #100]
	ldr r11, [r8, #260]
	orr r10, r10, r11
	eor r1, r1, r10
	ldr r10, [r9, #104]
	ldr r11, [r8, #264]
	orr r10, r10, r11
	eor r2, r2, r10
	ldr r10, [r9, #108]
	ldr r11, [r8, #268]
	orr r10, r10, r11
	eor r3, r3, r10
	ldr r10, [r9, #112]
	ldr r11, [r8, #272]
	orr r10, r10, r11
	eor r4, r4, r10
	ldr r10, [r9, #116]
	ldr r11, [r8, #276]
	orr r10, r10, r11
	eor r5, r5, r10
	ldr r10, [r9, #120]
	ldr r11, [r8, #280]
	orr r10, r10, r11
	eor r6, r6, r10
	ldr r10, [r9, #124]
	ldr r11, [r8, #284]
	orr r10, r10, r11
	eor r7, r7, r10
	ldr r10, [r9, #92]
	and r10, r10, r7
	ldr r11, [r8, #256]
	eor r11, r11, r10, ror #8
	str r11, [r8, #256]
	ldr r10, [r9, #64]
	and r10, r10, r0
	ldr r11, [r8, #260]
	eor r11, r11, r10
	str r11, [r8, #260]
	ldr r10, [r9, #68]
	and r10, r10, r1
	ldr r11, [r8, #264]
	eor r11, r11, r10
	str r11, [r8, #264]
	ldr r10, [r9, #72]
	and r10, r10, r2
	ldr r11, [r8, #268]
	eor r11, r11, r10
	str r11, [r8, #268]
	ldr r10, [r9, #76]
	and r10, r10, r3
	ldr r11, [r8, #272]
	eor r11, r11, r10
	str r11, [r8, #272]
	ldr r10, [r9, #80]
	and r10, r10, r4
	ldr r11, [r8, #276]
	eor r11, r11, r10
	str r11, [r8, #276]
	ldr r10, [r9, #84]
	and r10, r10, r5
	ldr r11, [r8, #280]
	eor r11, r11, r10
	str r11, [r8, #280]
	ldr r10, [r9, #88]
	and r10, r10, r6
	ldr r11, [r8, #284]
	eor r11, r11, r10
	str r11, [r8, #284]
	str r0, [r8, #224]
	str r1, [r8, #228]
	str r2, [r8, #232]
	str r3, [r8, #236]
	str r4, [r8, #240]
	str r5, [r8, #244]
	str r6, [r8, #248]
	str r7, [r8, #252]
	ldr r0, [r8, #160]
	ldr r1, [r8, #164]
	ldr r2, [r8, #168]
	ldr r3, [r8, #172]
	ldr r4, [r8, #176]
	ldr r5, [r8, #180]
	ldr r6, [r8, #184]
	ldr r7, [r8, #188]
	ldr r10, [r9, #28]
	and r10, r10, r7
	ldr r11, [r8, #192]
	eor r11, r11, r10, ror #8
	str r11, [r8, #192]
	ldr r10, [r9, #0]
	and r10, r10, r0
	ldr r11, [r8, #196]
	eor r11, r11, r10
	str r11, [r8, #196]
	ldr r10, [r9, #4]
	and r10, r10, r1
	ldr r11, [r8, #200]
	eor r11, r11, r10
	str r11, [r8, #200]
	ldr r10, [r9, #8]
	and r10, r10, r2
	ldr r11, [r8, #204]
	eor r11, r11, r10
	str r11, [r8, #204]
	ldr r10, [r9, #12]
	and r10, r10, r3
	ldr r11, [r8, #208]
	eor r11, r11, r10
	str r11, [r8, #208]
	ldr r10, [r9, #16]
	and r10, r10, r4
	ldr r11, [r8, #212]
	eor r11, r11, r10
	str r11, [r8, #212]
	ldr r10, [r9, #20]
	and r10, r10, r5
	ldr r11, [r8, #216]
	eor r11, r11, r10
	str r11, [r8, #216]
	ldr r10, [r9, #24]
	and r10, r10, r6
	ldr r11, [r8, #220]
	eor r11, r11, r10
	str r11, [r8, #220]
	ldr r10, [r9, #32]
	ldr r11, [r8, #192]
	orr r10, r10, r11
	eor r0, r0, r10
	ldr r10, [r9, #36]
	ldr r11, [r8, #196]
	orr r10, r10, r11
	eor r1, r1, r10
	ldr r10, [r9, #40]
	ldr r11, [r8, #200]
	orr r10, r10, r11
	eor r2, r2, r10
	ldr r10, [r9, #44]
	ldr r11, [r8, #204]
	orr r10, r10, r11
	eor r3, r3, r10
	ldr r10, [r9, #48]
	ldr r11, [r8, #208]
	orr r10, r10, r11
	eor r4, r4, r10
	ldr r10, [r9, #52]
	ldr r11, [r8, #212]
	orr r10, r10, r11
	eor r5, r5, r10
	ldr r10, [r9, #56]
	ldr r11, [r8, #216]
	orr r10, r10, r11
	eor r6, r6, r10
	ldr r10, [r9, #60]
	ldr r11, [r8, #220]
	orr r10, r10, r11
	eor r7, r7, r10
	str r0, [r8, #160]
	str r1, [r8, #164]
	str r2, [r8, #168]
	str r3, [r8, #172]
	str r4, [r8, #176]
	str r5, [r8, #180]
	str r6, [r8, #184]
	str r7, [r8, #188]
	add r9, r9, #128
212:
	ldr r10, [r8, #2468]
	cmp r9, r10
	bne 29b
	ldr r11, [r8, #224]
	ldr r10, [r9, #0]
	eor r11, r11, r10
	str r11, [r8, #224]
	ldr r11, [r8, #228]
	ldr r10, [r9, #4]
	eor r11, r11, r10
	str r11, [r8, #228]
	ldr r11, [r8, #232]
	ldr r10, [r9, #8]
	eor r11, r11, r10
	str r11, [r8, #232]
	ldr r11, [r8, #236]
	ldr r10, [r9, #12]
	eor r11, r11, r10
	str r11, [r8, #236]
	ldr r11, [r8, #240]
	ldr r10, [r9, #16]
	eor r11, r11, r10
	str r11, [r8, #240]
	ldr r11, [r8, #244]
	ldr r10, [r9, #20]
	eor r11, r11, r10
	str r11, [r8, #244]
	ldr r11, [r8, #248]
	ldr r10, [r9, #24]
	eor r11, r11, r10
	str r11, [r8, #248]
	ldr r11, [r8, #252]
	ldr r10, [r9, #28]
	eor r11, r11, r10
	str r11, [r8, #252]
	ldr r11, [r8, #256]
	ldr r10, [r9, #32]
	eor r11, r11, r10
	str r11, [r8, #256]
	ldr r11, [r8, #260]
	ldr r10, [r9, #36]
	eor r11, r11, r10
	str r11, [r8, #260]
	ldr r11, [r8, #264]
	ldr r10, [r9, #40]
	eor r11, r11, r10
	str r11, [r8, #264]
	ldr r11, [r8, #268]
	ldr r10, [r9, #44]
	eor r11, r11, r10
	str r11, [r8, #268]
	ldr r11, [r8, #272]
	ldr r10, [r9, #48]
	eor r11, r11, r10
	str r11, [r8, #272]
	ldr r11, [r8, #276]
	ldr r10, [r9, #52]
	eor r11, r11, r10
	str r11, [r8, #276]
	ldr r11, [r8, #280]
	ldr r10, [r9, #56]
	eor r11, r11, r10
	str r11, [r8, #280]
	ldr r11, [r8, #284]
	ldr r10, [r9, #60]
	eor r11, r11, r10
	str r11, [r8, #284]
	ldr r11, [r8, #160]
	ldr r10, [r9, #64]
	eor r11, r11, r10
	str r11, [r8, #160]
	ldr r11, [r8, #164]
	ldr r10, [r9, #68]
	eor r11, r11, r10
	str r11, [r8, #164]
	ldr r11, [r8, #168]
	ldr r10, [r9, #72]
	eor r11, r11, r10
	str r11, [r8, #168]
	ldr r11, [r8, #172]
	ldr r10, [r9, #76]
	eor r11, r11, r10
	str r11, [r8, #172]
	ldr r11, [r8, #176]
	ldr r10, [r9, #80]
	eor r11, r11, r10
	str r11, [r8, #176]
	ldr r11, [r8, #180]
	ldr r10, [r9, #84]
	eor r11, r11, r10
	str r11, [r8, #180]
	ldr r11, [r8, #184]
	ldr r10, [r9, #88]
	eor r11, r11, r10
	str r11, [r8, #184]
	ldr r11, [r8, #188]
	ldr r10, [r9, #92]
	eor r11, r11, r10
	str r11, [r8, #188]
	ldr r11, [r8, #192]
	ldr r10, [r9, #96]
	eor r11, r11, r10
	str r11, [r8, #192]
	ldr r11, [r8, #196]
	ldr r10, [r9, #100]
	eor r11, r11, r10
	str r11, [r8, #196]
	ldr r11, [r8, #200]
	ldr r10, [r9, #104]
	eor r11, r11, r10
	str r11, [r8, #200]
	ldr r11, [r8, #204]
	ldr r10, [r9, #108]
	eor r11, r11, r10
	str r11, [r8, #204]
	ldr r11, [r8, #208]
	ldr r10, [r9, #112]
	eor r11, r11, r10
	str r11, [r8, #208]
	ldr r11, [r8, #212]
	ldr r10, [r9, #116]
	eor r11, r11, r10
	str r11, [r8, #212]
	ldr r11, [r8, #216]
	ldr r10, [r9, #120]
	eor r11, r11, r10
	str r11, [r8, #216]
	ldr r11, [r8, #220]
	ldr r10, [r9, #124]
	eor r11, r11, r10
	str r11, [r8, #220]
	ldr r0, [r8, #224]
	ldr r1, [r8, #228]
	ldr r2, [r8, #232]
	ldr r3, [r8, #236]
	ldr r4, [r8, #240]
	ldr r5, [r8, #244]
	ldr r6, [r8, #248]
	ldr r7, [r8, #252]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2528]
	str r1, [r8, #2544]
	str r2, [r8, #2560]
	str r3, [r8, #2576]
	str r4, [r8, #2592]
	str r5, [r8, #2608]
	str r6, [r8, #2624]
	str r7, [r8, #2640]
	ldr r0, [r8, #256]
	ldr r1, [r8, #260]
	ldr r2, [r8, #264]
	ldr r3, [r8, #268]
	ldr r4, [r8, #272]
	ldr r5, [r8, #276]
	ldr r6, [r8, #280]
	ldr r7, [r8, #284]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2532]
	str r1, [r8, #2548]
	str r2, [r8, #2564]
	str r3, [r8, #2580]
	str r4, [r8, #2596]
	str r5, [r8, #2612]
	str r6, [r8, #2628]
	str r7, [r8, #2644]
	ldr r0, [r8, #160]
	ldr r1, [r8, #164]
	ldr r2, [r8, #168]
	ldr r3, [r8, #172]
	ldr r4, [r8, #176]
	ldr r5, [r8, #180]
	ldr r6, [r8, #184]
	ldr r7, [r8, #188]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2536]
	str r1, [r8, #2552]
	str r2, [r8, #2568]
	str r3, [r8, #2584]
	str r4, [r8, #2600]
	str r5, [r8, #2616]
	str r6, [r8, #2632]
	str r7, [r8, #2648]
	ldr r0, [r8, #192]
	ldr r1, [r8, #196]
	ldr r2, [r8, #200]
	ldr r3, [r8, #204]
	ldr r4, [r8, #208]
	ldr r5, [r8, #212]
	ldr r6, [r8, #216]
	ldr r7, [r8, #220]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2540]
	str r1, [r8, #2556]
	str r2, [r8, #2572]
	str r3, [r8, #2588]
	str r4, [r8, #2604]
	str r5, [r8, #2620]
	str r6, [r8, #2636]
	str r7, [r8, #2652]
	ldr r1, [r8, #2508]
	ldr r2, [r8, #2512]
	ldr lr, [r8, #2468]
	lsr r10, r2, #3
	cmp r10, #0
	bne 213f
	mov r3, r2
	b 214f
213:
	mov r3, #8
214:
	add r0, r8, #2528
	mov r12, r1
215:
	ldr r10, [r0, #0]
	str r10, [r12, #0]
	ldr r10, [r0, #4]
	str r10, [r12, #4]
	ldr r10, [r0, #8]
	str r10, [r12, #8]
	ldr r10, [r0, #12]
	str r10, [r12, #12]
	add r0, r0, #16
	add r12, r12, #16
	subs r3, r3, #1
	bne 215b
	lsr r10, r2, #3
	cmp r10, #0
	bne 216f
	mov r3, r2
	b 217f
216:
	mov r3, #8
217:
	add r1, r1, #128
	subs r2, r2, r3
	bne 25b
	b 24f
23:
24:
	mov r12, r8
	ldr r4, [r12, #2472]
	ldr r5, [r12, #2476]
	ldr r6, [r12, #2480]
	ldr r7, [r12, #2484]
	ldr r8, [r12, #2488]
	ldr r9, [r12, #2492]
	ldr r10, [r12, #2496]
	ldr r11, [r12, #2500]
	ldr lr, [r12, #2504]
	add r12, sp, #8
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	str r2, [r12, #32]
	str r2, [r12, #36]
	str r2, [r12, #40]
	str r2, [r12, #44]
	str r2, [r12, #48]
	str r2, [r12, #52]
	str r2, [r12, #56]
	str r2, [r12, #60]
	str r2, [r12, #64]
	str r2, [r12, #68]
	str r2, [r12, #72]
	str r2, [r12, #76]
	str r2, [r12, #80]
	str r2, [r12, #84]
	str r2, [r12, #88]
	str r2, [r12, #92]
	str r2, [r12, #96]
	str r2, [r12, #100]
	str r2, [r12, #104]
	str r2, [r12, #108]
	str r2, [r12, #112]
	str r2, [r12, #116]
	str r2, [r12, #120]
	str r2, [r12, #124]
	str r2, [r12, #128]
	str r2, [r12, #132]
	str r2, [r12, #136]
	str r2, [r12, #140]
	str r2, [r12, #144]
	str r2, [r12, #148]
	str r2, [r12, #152]
	str r2, [r12, #156]
	str r2, [r12, #160]
	str r2, [r12, #164]
	str r2, [r12, #168]
	str r2, [r12, #172]
	str r2, [r12, #176]
	str r2, [r12, #180]
	str r2, [r12, #184]
	str r2, [r12, #188]
	str r2, [r12, #192]
	str r2, [r12, #196]
	str r2, [r12, #200]
	str r2, [r12, #204]
	str r2, [r12, #208]
	str r2, [r12, #212]
	str r2, [r12, #216]
	str r2, [r12, #220]
	str r2, [r12, #224]
	str r2, [r12, #228]
	str r2, [r12, #232]
	str r2, [r12, #236]
	str r2, [r12, #240]
	str r2, [r12, #244]
	str r2, [r12, #248]
	str r2, [r12, #252]
	str r2, [r12, #256]
	str r2, [r12, #260]
	str r2, [r12, #264]
	str r2, [r12, #268]
	str r2, [r12, #272]
	str r2, [r12, #276]
	str r2, [r12, #280]
	str r2, [r12, #284]
	str r2, [r12, #288]
	str r2, [r12, #292]
	str r2, [r12, #296]
	str r2, [r12, #300]
	str r2, [r12, #304]
	str r2, [r12, #308]
	str r2, [r12, #312]
	str r2, [r12, #316]
	str r2, [r12, #320]
	str r2, [r12, #324]
	str r2, [r12, #328]
	str r2, [r12, #332]
	str r2, [r12, #336]
	str r2, [r12, #340]
	str r2, [r12, #344]
	str r2, [r12, #348]
	str r2, [r12, #352]
	str r2, [r12, #356]
	str r2, [r12, #360]
	str r2, [r12, #364]
	str r2, [r12, #368]
	str r2, [r12, #372]
	str r2, [r12, #376]
	str r2, [r12, #380]
	str r2, [r12, #384]
	str r2, [r12, #388]
	str r2, [r12, #392]
	str r2, [r12, #396]
	str r2, [r12, #400]
	str r2, [r12, #404]
	str r2, [r12, #408]
	str r2, [r12, #412]
	str r2, [r12, #416]
	str r2, [r12, #420]
	str r2, [r12, #424]
	str r2, [r12, #428]
	str r2, [r12, #432]
	str r2, [r12, #436]
	str r2, [r12, #440]
	str r2, [r12, #444]
	str r2, [r12, #448]
	str r2, [r12, #452]
	str r2, [r12, #456]
	str r2, [r12, #460]
	str r2, [r12, #464]
	str r2, [r12, #468]
	str r2, [r12, #472]
	str r2, [r12, #476]
	str r2, [r12, #480]
	str r2, [r12, #484]
	str r2, [r12, #488]
	str r2, [r12, #492]
	str r2, [r12, #496]
	str r2, [r12, #500]
	str r2, [r12, #504]
	str r2, [r12, #508]
	str r2, [r12, #512]
	str r2, [r12, #516]
	str r2, [r12, #520]
	str r2, [r12, #524]
	str r2, [r12, #528]
	str r2, [r12, #532]
	str r2, [r12, #536]
	str r2, [r12, #540]
	str r2, [r12, #544]
	str r2, [r12, #548]
	str r2, [r12, #552]
	str r2, [r12, #556]
	str r2, [r12, #560]
	str r2, [r12, #564]
	str r2, [r12, #568]
	str r2, [r12, #572]
	str r2, [r12, #576]
	str r2, [r12, #580]
	str r2, [r12, #584]
	str r2, [r12, #588]
	str r2, [r12, #592]
	str r2, [r12, #596]
	str r2, [r12, #600]
	str r2, [r12, #604]
	str r2, [r12, #608]
	str r2, [r12, #612]
	str r2, [r12, #616]
	str r2, [r12, #620]
	str r2, [r12, #624]
	str r2, [r12, #628]
	str r2, [r12, #632]
	str r2, [r12, #636]
	str r2, [r12, #640]
	str r2, [r12, #644]
	str r2, [r12, #648]
	str r2, [r12, #652]
	str r2, [r12, #656]
	str r2, [r12, #660]
	str r2, [r12, #664]
	str r2, [r12, #668]
	str r2, [r12, #672]
	str r2, [r12, #676]
	str r2, [r12, #680]
	str r2, [r12, #684]
	str r2, [r12, #688]
	str r2, [r12, #692]
	str r2, [r12, #696]
	str r2, [r12, #700]
	str r2, [r12, #704]
	str r2, [r12, #708]
	str r2, [r12, #712]
	str r2, [r12, #716]
	str r2, [r12, #720]
	str r2, [r12, #724]
	str r2, [r12, #728]
	str r2, [r12, #732]
	str r2, [r12, #736]
	str r2, [r12, #740]
	str r2, [r12, #744]
	str r2, [r12, #748]
	str r2, [r12, #752]
	str r2, [r12, #756]
	str r2, [r12, #760]
	str r2, [r12, #764]
	str r2, [r12, #768]
	str r2, [r12, #772]
	str r2, [r12, #776]
	str r2, [r12, #780]
	str r2, [r12, #784]
	str r2, [r12, #788]
	str r2, [r12, #792]
	str r2, [r12, #796]
	str r2, [r12, #800]
	str r2, [r12, #804]
	str r2, [r12, #808]
	str r2, [r12, #812]
	str r2, [r12, #816]
	str r2, [r12, #820]
	str r2, [r12, #824]
	str r2, [r12, #828]
	str r2, [r12, #832]
	str r2, [r12, #836]
	str r2, [r12, #840]
	str r2, [r12, #844]
	str r2, [r12, #848]
	str r2, [r12, #852]
	str r2, [r12, #856]
	str r2, [r12, #860]
	str r2, [r12, #864]
	str r2, [r12, #868]
	str r2, [r12, #872]
	str r2, [r12, #876]
	str r2, [r12, #880]
	str r2, [r12, #884]
	str r2, [r12, #888]
	str r2, [r12, #892]
	str r2, [r12, #896]
	str r2, [r12, #900]
	str r2, [r12, #904]
	str r2, [r12, #908]
	str r2, [r12, #912]
	str r2, [r12, #916]
	str r2, [r12, #920]
	str r2, [r12, #924]
	str r2, [r12, #928]
	str r2, [r12, #932]
	str r2, [r12, #936]
	str r2, [r12, #940]
	str r2, [r12, #944]
	str r2, [r12, #948]
	str r2, [r12, #952]
	str r2, [r12, #956]
	str r2, [r12, #960]
	str r2, [r12, #964]
	str r2, [r12, #968]
	str r2, [r12, #972]
	str r2, [r12, #976]
	str r2, [r12, #980]
	str r2, [r12, #984]
	str r2, [r12, #988]
	str r2, [r12, #992]
	str r2, [r12, #996]
	str r2, [r12, #1000]
	str r2, [r12, #1004]
	str r2, [r12, #1008]
	str r2, [r12, #1012]
	str r2, [r12, #1016]
	str r2, [r12, #1020]
	str r2, [r12, #1024]
	str r2, [r12, #1028]
	str r2, [r12, #1032]
	str r2, [r12, #1036]
	str r2, [r12, #1040]
	str r2, [r12, #1044]
	str r2, [r12, #1048]
	str r2, [r12, #1052]
	str r2, [r12, #1056]
	str r2, [r12, #1060]
	str r2, [r12, #1064]
	str r2, [r12, #1068]
	str r2, [r12, #1072]
	str r2, [r12, #1076]
	str r2, [r12, #1080]
	str r2, [r12, #1084]
	str r2, [r12, #1088]
	str r2, [r12, #1092]
	str r2, [r12, #1096]
	str r2, [r12, #1100]
	str r2, [r12, #1104]
	str r2, [r12, #1108]
	str r2, [r12, #1112]
	str r2, [r12, #1116]
	str r2, [r12, #1120]
	str r2, [r12, #1124]
	str r2, [r12, #1128]
	str r2, [r12, #1132]
	str r2, [r12, #1136]
	str r2, [r12, #1140]
	str r2, [r12, #1144]
	str r2, [r12, #1148]
	str r2, [r12, #1152]
	str r2, [r12, #1156]
	str r2, [r12, #1160]
	str r2, [r12, #1164]
	str r2, [r12, #1168]
	str r2, [r12, #1172]
	str r2, [r12, #1176]
	str r2, [r12, #1180]
	str r2, [r12, #1184]
	str r2, [r12, #1188]
	str r2, [r12, #1192]
	str r2, [r12, #1196]
	str r2, [r12, #1200]
	str r2, [r12, #1204]
	str r2, [r12, #1208]
	str r2, [r12, #1212]
	str r2, [r12, #1216]
	str r2, [r12, #1220]
	str r2, [r12, #1224]
	str r2, [r12, #1228]
	str r2, [r12, #1232]
	str r2, [r12, #1236]
	str r2, [r12, #1240]
	str r2, [r12, #1244]
	str r2, [r12, #1248]
	str r2, [r12, #1252]
	str r2, [r12, #1256]
	str r2, [r12, #1260]
	str r2, [r12, #1264]
	str r2, [r12, #1268]
	str r2, [r12, #1272]
	str r2, [r12, #1276]
	str r2, [r12, #1280]
	str r2, [r12, #1284]
	str r2, [r12, #1288]
	str r2, [r12, #1292]
	str r2, [r12, #1296]
	str r2, [r12, #1300]
	str r2, [r12, #1304]
	str r2, [r12, #1308]
	str r2, [r12, #1312]
	str r2, [r12, #1316]
	str r2, [r12, #1320]
	str r2, [r12, #1324]
	str r2, [r12, #1328]
	str r2, [r12, #1332]
	str r2, [r12, #1336]
	str r2, [r12, #1340]
	str r2, [r12, #1344]
	str r2, [r12, #1348]
	str r2, [r12, #1352]
	str r2, [r12, #1356]
	str r2, [r12, #1360]
	str r2, [r12, #1364]
	str r2, [r12, #1368]
	str r2, [r12, #1372]
	str r2, [r12, #1376]
	str r2, [r12, #1380]
	str r2, [r12, #1384]
	str r2, [r12, #1388]
	str r2, [r12, #1392]
	str r2, [r12, #1396]
	str r2, [r12, #1400]
	str r2, [r12, #1404]
	str r2, [r12, #1408]
	str r2, [r12, #1412]
	str r2, [r12, #1416]
	str r2, [r12, #1420]
	str r2, [r12, #1424]
	str r2, [r12, #1428]
	str r2, [r12, #1432]
	str r2, [r12, #1436]
	str r2, [r12, #1440]
	str r2, [r12, #1444]
	str r2, [r12, #1448]
	str r2, [r12, #1452]
	str r2, [r12, #1456]
	str r2, [r12, #1460]
	str r2, [r12, #1464]
	str r2, [r12, #1468]
	str r2, [r12, #1472]
	str r2, [r12, #1476]
	str r2, [r12, #1480]
	str r2, [r12, #1484]
	str r2, [r12, #1488]
	str r2, [r12, #1492]
	str r2, [r12, #1496]
	str r2, [r12, #1500]
	str r2, [r12, #1504]
	str r2, [r12, #1508]
	str r2, [r12, #1512]
	str r2, [r12, #1516]
	str r2, [r12, #1520]
	str r2, [r12, #1524]
	str r2, [r12, #1528]
	str r2, [r12, #1532]
	str r2, [r12, #1536]
	str r2, [r12, #1540]
	str r2, [r12, #1544]
	str r2, [r12, #1548]
	str r2, [r12, #1552]
	str r2, [r12, #1556]
	str r2, [r12, #1560]
	str r2, [r12, #1564]
	str r2, [r12, #1568]
	str r2, [r12, #1572]
	str r2, [r12, #1576]
	str r2, [r12, #1580]
	str r2, [r12, #1584]
	str r2, [r12, #1588]
	str r2, [r12, #1592]
	str r2, [r12, #1596]
	str r2, [r12, #1600]
	str r2, [r12, #1604]
	str r2, [r12, #1608]
	str r2, [r12, #1612]
	str r2, [r12, #1616]
	str r2, [r12, #1620]
	str r2, [r12, #1624]
	str r2, [r12, #1628]
	str r2, [r12, #1632]
	str r2, [r12, #1636]
	str r2, [r12, #1640]
	str r2, [r12, #1644]
	str r2, [r12, #1648]
	str r2, [r12, #1652]
	str r2, [r12, #1656]
	str r2, [r12, #1660]
	str r2, [r12, #1664]
	str r2, [r12, #1668]
	str r2, [r12, #1672]
	str r2, [r12, #1676]
	str r2, [r12, #1680]
	str r2, [r12, #1684]
	str r2, [r12, #1688]
	str r2, [r12, #1692]
	str r2, [r12, #1696]
	str r2, [r12, #1700]
	str r2, [r12, #1704]
	str r2, [r12, #1708]
	str r2, [r12, #1712]
	str r2, [r12, #1716]
	str r2, [r12, #1720]
	str r2, [r12, #1724]
	str r2, [r12, #1728]
	str r2, [r12, #1732]
	str r2, [r12, #1736]
	str r2, [r12, #1740]
	str r2, [r12, #1744]
	str r2, [r12, #1748]
	str r2, [r12, #1752]
	str r2, [r12, #1756]
	str r2, [r12, #1760]
	str r2, [r12, #1764]
	str r2, [r12, #1768]
	str r2, [r12, #1772]
	str r2, [r12, #1776]
	str r2, [r12, #1780]
	str r2, [r12, #1784]
	str r2, [r12, #1788]
	str r2, [r12, #1792]
	str r2, [r12, #1796]
	str r2, [r12, #1800]
	str r2, [r12, #1804]
	str r2, [r12, #1808]
	str r2, [r12, #1812]
	str r2, [r12, #1816]
	str r2, [r12, #1820]
	str r2, [r12, #1824]
	str r2, [r12, #1828]
	str r2, [r12, #1832]
	str r2, [r12, #1836]
	str r2, [r12, #1840]
	str r2, [r12, #1844]
	str r2, [r12, #1848]
	str r2, [r12, #1852]
	str r2, [r12, #1856]
	str r2, [r12, #1860]
	str r2, [r12, #1864]
	str r2, [r12, #1868]
	str r2, [r12, #1872]
	str r2, [r12, #1876]
	str r2, [r12, #1880]
	str r2, [r12, #1884]
	str r2, [r12, #1888]
	str r2, [r12, #1892]
	str r2, [r12, #1896]
	str r2, [r12, #1900]
	str r2, [r12, #1904]
	str r2, [r12, #1908]
	str r2, [r12, #1912]
	str r2, [r12, #1916]
	str r2, [r12, #1920]
	str r2, [r12, #1924]
	str r2, [r12, #1928]
	str r2, [r12, #1932]
	str r2, [r12, #1936]
	str r2, [r12, #1940]
	str r2, [r12, #1944]
	str r2, [r12, #1948]
	str r2, [r12, #1952]
	str r2, [r12, #1956]
	str r2, [r12, #1960]
	str r2, [r12, #1964]
	str r2, [r12, #1968]
	str r2, [r12, #1972]
	str r2, [r12, #1976]
	str r2, [r12, #1980]
	str r2, [r12, #1984]
	str r2, [r12, #1988]
	str r2, [r12, #1992]
	str r2, [r12, #1996]
	str r2, [r12, #2000]
	str r2, [r12, #2004]
	str r2, [r12, #2008]
	str r2, [r12, #2012]
	str r2, [r12, #2016]
	str r2, [r12, #2020]
	str r2, [r12, #2024]
	str r2, [r12, #2028]
	str r2, [r12, #2032]
	str r2, [r12, #2036]
	str r2, [r12, #2040]
	str r2, [r12, #2044]
	str r2, [r12, #2048]
	str r2, [r12, #2052]
	str r2, [r12, #2056]
	str r2, [r12, #2060]
	str r2, [r12, #2064]
	str r2, [r12, #2068]
	str r2, [r12, #2072]
	str r2, [r12, #2076]
	str r2, [r12, #2080]
	str r2, [r12, #2084]
	str r2, [r12, #2088]
	str r2, [r12, #2092]
	str r2, [r12, #2096]
	str r2, [r12, #2100]
	str r2, [r12, #2104]
	str r2, [r12, #2108]
	str r2, [r12, #2112]
	str r2, [r12, #2116]
	str r2, [r12, #2120]
	str r2, [r12, #2124]
	str r2, [r12, #2128]
	str r2, [r12, #2132]
	str r2, [r12, #2136]
	str r2, [r12, #2140]
	str r2, [r12, #2144]
	str r2, [r12, #2148]
	str r2, [r12, #2152]
	str r2, [r12, #2156]
	str r2, [r12, #2160]
	str r2, [r12, #2164]
	str r2, [r12, #2168]
	str r2, [r12, #2172]
	str r2, [r12, #2176]
	str r2, [r12, #2180]
	str r2, [r12, #2184]
	str r2, [r12, #2188]
	str r2, [r12, #2192]
	str r2, [r12, #2196]
	str r2, [r12, #2200]
	str r2, [r12, #2204]
	str r2, [r12, #2208]
	str r2, [r12, #2212]
	str r2, [r12, #2216]
	str r2, [r12, #2220]
	str r2, [r12, #2224]
	str r2, [r12, #2228]
	str r2, [r12, #2232]
	str r2, [r12, #2236]
	str r2, [r12, #2240]
	str r2, [r12, #2244]
	str r2, [r12, #2248]
	str r2, [r12, #2252]
	str r2, [r12, #2256]
	str r2, [r12, #2260]
	str r2, [r12, #2264]
	str r2, [r12, #2268]
	str r2, [r12, #2272]
	str r2, [r12, #2276]
	str r2, [r12, #2280]
	str r2, [r12, #2284]
	str r2, [r12, #2288]
	str r2, [r12, #2292]
	str r2, [r12, #2296]
	str r2, [r12, #2300]
	str r2, [r12, #2304]
	str r2, [r12, #2308]
	str r2, [r12, #2312]
	str r2, [r12, #2316]
	str r2, [r12, #2320]
	str r2, [r12, #2324]
	str r2, [r12, #2328]
	str r2, [r12, #2332]
	str r2, [r12, #2336]
	str r2, [r12, #2340]
	str r2, [r12, #2344]
	str r2, [r12, #2348]
	str r2, [r12, #2352]
	str r2, [r12, #2356]
	str r2, [r12, #2360]
	str r2, [r12, #2364]
	str r2, [r12, #2368]
	str r2, [r12, #2372]
	str r2, [r12, #2376]
	str r2, [r12, #2380]
	str r2, [r12, #2384]
	str r2, [r12, #2388]
	str r2, [r12, #2392]
	str r2, [r12, #2396]
	str r2, [r12, #2400]
	str r2, [r12, #2404]
	str r2, [r12, #2408]
	str r2, [r12, #2412]
	str r2, [r12, #2416]
	str r2, [r12, #2420]
	str r2, [r12, #2424]
	str r2, [r12, #2428]
	str r2, [r12, #2432]
	str r2, [r12, #2436]
	str r2, [r12, #2440]
	str r2, [r12, #2444]
	str r2, [r12, #2448]
	str r2, [r12, #2452]
	str r2, [r12, #2456]
	str r2, [r12, #2460]
	str r2, [r12, #2464]
	str r2, [r12, #2468]
	str r2, [r12, #2472]
	str r2, [r12, #2476]
	str r2, [r12, #2480]
	str r2, [r12, #2484]
	str r2, [r12, #2488]
	str r2, [r12, #2492]
	str r2, [r12, #2496]
	str r2, [r12, #2500]
	str r2, [r12, #2504]
	str r2, [r12, #2508]
	str r2, [r12, #2512]
	str r2, [r12, #2516]
	str r2, [r12, #2520]
	str r2, [r12, #2524]
	str r2, [r12, #2528]
	str r2, [r12, #2532]
	str r2, [r12, #2536]
	str r2, [r12, #2540]
	str r2, [r12, #2544]
	str r2, [r12, #2548]
	str r2, [r12, #2552]
	str r2, [r12, #2556]
	str r2, [r12, #2560]
	str r2, [r12, #2564]
	str r2, [r12, #2568]
	str r2, [r12, #2572]
	str r2, [r12, #2576]
	str r2, [r12, #2580]
	str r2, [r12, #2584]
	str r2, [r12, #2588]
	str r2, [r12, #2592]
	str r2, [r12, #2596]
	str r2, [r12, #2600]
	str r2, [r12, #2604]
	str r2, [r12, #2608]
	str r2, [r12, #2612]
	str r2, [r12, #2616]
	str r2, [r12, #2620]
	str r2, [r12, #2624]
	str r2, [r12, #2628]
	str r2, [r12, #2632]
	str r2, [r12, #2636]
	str r2, [r12, #2640]
	str r2, [r12, #2644]
	str r2, [r12, #2648]
	str r2, [r12, #2652]
	str r2, [r12, #2656]
	str r2, [r12, #2660]
	str r2, [r12, #2664]
	str r2, [r12, #2668]
	str r2, [r12, #2672]
	str r2, [r12, #2676]
	str r2, [r12, #2680]
	str r2, [r12, #2684]
	str r2, [r12, #2688]
	str r2, [r12, #2692]
	str r2, [r12, #2696]
	str r2, [r12, #2700]
	str r2, [r12, #2704]
	str r2, [r12, #2708]
	str r2, [r12, #2712]
	str r2, [r12, #2716]
	add sp, sp, #2816
	bx lr
