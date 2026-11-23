// The functions of `src/ec_p521_compressed.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p521_compress_public_key:
	mov r12, r2
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
	ldr r4, [r1, #62]
	rev r4, r4
	str r4, [r12, #2296]
	ldr r4, [r1, #58]
	rev r4, r4
	str r4, [r12, #2300]
	ldr r4, [r1, #54]
	rev r4, r4
	str r4, [r12, #2304]
	ldr r4, [r1, #50]
	rev r4, r4
	str r4, [r12, #2308]
	ldr r4, [r1, #46]
	rev r4, r4
	str r4, [r12, #2312]
	ldr r4, [r1, #42]
	rev r4, r4
	str r4, [r12, #2316]
	ldr r4, [r1, #38]
	rev r4, r4
	str r4, [r12, #2320]
	ldr r4, [r1, #34]
	rev r4, r4
	str r4, [r12, #2324]
	ldr r4, [r1, #30]
	rev r4, r4
	str r4, [r12, #2328]
	ldr r4, [r1, #26]
	rev r4, r4
	str r4, [r12, #2332]
	ldr r4, [r1, #22]
	rev r4, r4
	str r4, [r12, #2336]
	ldr r4, [r1, #18]
	rev r4, r4
	str r4, [r12, #2340]
	ldr r4, [r1, #14]
	rev r4, r4
	str r4, [r12, #2344]
	ldr r4, [r1, #10]
	rev r4, r4
	str r4, [r12, #2348]
	ldr r4, [r1, #6]
	rev r4, r4
	str r4, [r12, #2352]
	ldr r4, [r1, #2]
	rev r4, r4
	str r4, [r12, #2356]
	ldr r4, [r1, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2360]
	mov r4, #0
	str r4, [r12, #2364]
	ldr r4, [r1, #62]
	rev r4, r4
	str r4, [r12, #2368]
	ldr r4, [r1, #58]
	rev r4, r4
	str r4, [r12, #2372]
	ldr r4, [r1, #54]
	rev r4, r4
	str r4, [r12, #2376]
	ldr r4, [r1, #50]
	rev r4, r4
	str r4, [r12, #2380]
	ldr r4, [r1, #46]
	rev r4, r4
	str r4, [r12, #2384]
	ldr r4, [r1, #42]
	rev r4, r4
	str r4, [r12, #2388]
	ldr r4, [r1, #38]
	rev r4, r4
	str r4, [r12, #2392]
	ldr r4, [r1, #34]
	rev r4, r4
	str r4, [r12, #2396]
	ldr r4, [r1, #30]
	rev r4, r4
	str r4, [r12, #2400]
	ldr r4, [r1, #26]
	rev r4, r4
	str r4, [r12, #2404]
	ldr r4, [r1, #22]
	rev r4, r4
	str r4, [r12, #2408]
	ldr r4, [r1, #18]
	rev r4, r4
	str r4, [r12, #2412]
	ldr r4, [r1, #14]
	rev r4, r4
	str r4, [r12, #2416]
	ldr r4, [r1, #10]
	rev r4, r4
	str r4, [r12, #2420]
	ldr r4, [r1, #6]
	rev r4, r4
	str r4, [r12, #2424]
	ldr r4, [r1, #2]
	rev r4, r4
	str r4, [r12, #2428]
	ldr r4, [r1, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2432]
	mov r4, #0
	str r4, [r12, #2436]
	ldr r4, [r1, #62]
	rev r4, r4
	str r4, [r12, #2440]
	ldr r4, [r1, #58]
	rev r4, r4
	str r4, [r12, #2444]
	ldr r4, [r1, #54]
	rev r4, r4
	str r4, [r12, #2448]
	ldr r4, [r1, #50]
	rev r4, r4
	str r4, [r12, #2452]
	ldr r4, [r1, #46]
	rev r4, r4
	str r4, [r12, #2456]
	ldr r4, [r1, #42]
	rev r4, r4
	str r4, [r12, #2460]
	ldr r4, [r1, #38]
	rev r4, r4
	str r4, [r12, #2464]
	ldr r4, [r1, #34]
	rev r4, r4
	str r4, [r12, #2468]
	ldr r4, [r1, #30]
	rev r4, r4
	str r4, [r12, #2472]
	ldr r4, [r1, #26]
	rev r4, r4
	str r4, [r12, #2476]
	ldr r4, [r1, #22]
	rev r4, r4
	str r4, [r12, #2480]
	ldr r4, [r1, #18]
	rev r4, r4
	str r4, [r12, #2484]
	ldr r4, [r1, #14]
	rev r4, r4
	str r4, [r12, #2488]
	ldr r4, [r1, #10]
	rev r4, r4
	str r4, [r12, #2492]
	ldr r4, [r1, #6]
	rev r4, r4
	str r4, [r12, #2496]
	ldr r4, [r1, #2]
	rev r4, r4
	str r4, [r12, #2500]
	ldr r4, [r1, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2504]
	mov r4, #0
	str r4, [r12, #2508]
	movw r10, #:lower16:({VG_P521_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P521_FRAME_CONSTS}
2:
	add r10, pc
3:
	mov r9, r12
	mov r11, #17
20:
	sub r11, r11, #1
	ldr r4, [r10, #0]
	ldr r5, [r10, #4]
	str r4, [r9, #64]
	str r5, [r9, #68]
	ldr r4, [r10, #8]
	ldr r5, [r10, #12]
	str r4, [r9, #72]
	str r5, [r9, #76]
	ldr r4, [r10, #16]
	ldr r5, [r10, #20]
	str r4, [r9, #80]
	str r5, [r9, #84]
	ldr r4, [r10, #24]
	ldr r5, [r10, #28]
	str r4, [r9, #88]
	str r5, [r9, #92]
	ldr r4, [r10, #32]
	ldr r5, [r10, #36]
	str r4, [r9, #96]
	str r5, [r9, #100]
	ldr r4, [r10, #40]
	ldr r5, [r10, #44]
	str r4, [r9, #104]
	str r5, [r9, #108]
	ldr r4, [r10, #48]
	ldr r5, [r10, #52]
	str r4, [r9, #112]
	str r5, [r9, #116]
	ldr r4, [r10, #56]
	ldr r5, [r10, #60]
	str r4, [r9, #120]
	str r5, [r9, #124]
	ldr r4, [r10, #64]
	ldr r5, [r10, #68]
	str r4, [r9, #128]
	str r5, [r9, #132]
	add r10, r10, #72
	add r9, r9, #72
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #3232]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2872]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2876]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2880]
	movw r4, #16384
	movt r4, #0
	str r4, [r12, #2884]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2888]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2892]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2896]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2900]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2904]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2908]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2912]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2916]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2920]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2924]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2928]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2932]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2936]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2940]
	movw r4, #25479
	movt r4, #44632
	str r4, [r12, #2944]
	movw r4, #25935
	movt r4, #32788
	str r4, [r12, #2948]
	movw r4, #43039
	movt r4, #59957
	str r4, [r12, #2952]
	movw r4, #41615
	movt r4, #30967
	str r4, [r12, #2956]
	movw r4, #38426
	movt r4, #50206
	str r4, [r12, #2960]
	movw r4, #47599
	movt r4, #33690
	str r4, [r12, #2964]
	movw r4, #55519
	movt r4, #24221
	str r4, [r12, #2968]
	movw r4, #10592
	movt r4, #48523
	str r4, [r12, #2972]
	movw r4, #16201
	movt r4, #43254
	str r4, [r12, #2976]
	movw r4, #3228
	movt r4, #61611
	str r4, [r12, #2980]
	movw r4, #30852
	movt r4, #51399
	str r4, [r12, #2984]
	movw r4, #23108
	movt r4, #63964
	str r4, [r12, #2988]
	movw r4, #55690
	movt r4, #11724
	str r4, [r12, #2992]
	movw r4, #27961
	movt r4, #30545
	str r4, [r12, #2996]
	movw r4, #17056
	movt r4, #53339
	str r4, [r12, #3000]
	movw r4, #19728
	movt r4, #4041
	str r4, [r12, #3004]
	movw r4, #77
	movt r4, #0
	str r4, [r12, #3008]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3012]
	add r6, r1, #1
	ldr r4, [r6, #62]
	rev r4, r4
	str r4, [r12, #2440]
	ldr r4, [r6, #58]
	rev r4, r4
	str r4, [r12, #2444]
	ldr r4, [r6, #54]
	rev r4, r4
	str r4, [r12, #2448]
	ldr r4, [r6, #50]
	rev r4, r4
	str r4, [r12, #2452]
	ldr r4, [r6, #46]
	rev r4, r4
	str r4, [r12, #2456]
	ldr r4, [r6, #42]
	rev r4, r4
	str r4, [r12, #2460]
	ldr r4, [r6, #38]
	rev r4, r4
	str r4, [r12, #2464]
	ldr r4, [r6, #34]
	rev r4, r4
	str r4, [r12, #2468]
	ldr r4, [r6, #30]
	rev r4, r4
	str r4, [r12, #2472]
	ldr r4, [r6, #26]
	rev r4, r4
	str r4, [r12, #2476]
	ldr r4, [r6, #22]
	rev r4, r4
	str r4, [r12, #2480]
	ldr r4, [r6, #18]
	rev r4, r4
	str r4, [r12, #2484]
	ldr r4, [r6, #14]
	rev r4, r4
	str r4, [r12, #2488]
	ldr r4, [r6, #10]
	rev r4, r4
	str r4, [r12, #2492]
	ldr r4, [r6, #6]
	rev r4, r4
	str r4, [r12, #2496]
	ldr r4, [r6, #2]
	rev r4, r4
	str r4, [r12, #2500]
	ldr r4, [r6, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2504]
	mov r4, #0
	str r4, [r12, #2508]
	add r6, r6, #66
	ldr r4, [r6, #62]
	rev r4, r4
	str r4, [r12, #2656]
	ldr r4, [r6, #58]
	rev r4, r4
	str r4, [r12, #2660]
	ldr r4, [r6, #54]
	rev r4, r4
	str r4, [r12, #2664]
	ldr r4, [r6, #50]
	rev r4, r4
	str r4, [r12, #2668]
	ldr r4, [r6, #46]
	rev r4, r4
	str r4, [r12, #2672]
	ldr r4, [r6, #42]
	rev r4, r4
	str r4, [r12, #2676]
	ldr r4, [r6, #38]
	rev r4, r4
	str r4, [r12, #2680]
	ldr r4, [r6, #34]
	rev r4, r4
	str r4, [r12, #2684]
	ldr r4, [r6, #30]
	rev r4, r4
	str r4, [r12, #2688]
	ldr r4, [r6, #26]
	rev r4, r4
	str r4, [r12, #2692]
	ldr r4, [r6, #22]
	rev r4, r4
	str r4, [r12, #2696]
	ldr r4, [r6, #18]
	rev r4, r4
	str r4, [r12, #2700]
	ldr r4, [r6, #14]
	rev r4, r4
	str r4, [r12, #2704]
	ldr r4, [r6, #10]
	rev r4, r4
	str r4, [r12, #2708]
	ldr r4, [r6, #6]
	rev r4, r4
	str r4, [r12, #2712]
	ldr r4, [r6, #2]
	rev r4, r4
	str r4, [r12, #2716]
	ldr r4, [r6, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2720]
	mov r4, #0
	str r4, [r12, #2724]
	ldrb r4, [r1, #0]
	eor r4, r4, #4
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #2440]
	ldr r8, [r12, #64]
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
	ldr r7, [r12, #2444]
	ldr r8, [r12, #68]
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
	ldr r7, [r12, #2448]
	ldr r8, [r12, #72]
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
	ldr r7, [r12, #2452]
	ldr r8, [r12, #76]
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
	ldr r7, [r12, #2456]
	ldr r8, [r12, #80]
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
	ldr r7, [r12, #2460]
	ldr r8, [r12, #84]
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
	ldr r7, [r12, #2464]
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
	ldr r7, [r12, #2468]
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
	ldr r7, [r12, #2472]
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
	ldr r7, [r12, #2476]
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
	ldr r7, [r12, #2480]
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
	ldr r7, [r12, #2484]
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
	ldr r7, [r12, #2488]
	ldr r8, [r12, #112]
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
	ldr r7, [r12, #2492]
	ldr r8, [r12, #116]
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
	ldr r7, [r12, #2496]
	ldr r8, [r12, #120]
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
	ldr r7, [r12, #2500]
	ldr r8, [r12, #124]
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
	ldr r7, [r12, #2504]
	ldr r8, [r12, #128]
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
	ldr r7, [r12, #2508]
	ldr r8, [r12, #132]
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
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #2656]
	ldr r8, [r12, #64]
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
	ldr r7, [r12, #2660]
	ldr r8, [r12, #68]
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
	ldr r7, [r12, #2664]
	ldr r8, [r12, #72]
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
	ldr r7, [r12, #2668]
	ldr r8, [r12, #76]
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
	ldr r7, [r12, #2672]
	ldr r8, [r12, #80]
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
	ldr r7, [r12, #2676]
	ldr r8, [r12, #84]
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
	ldr r7, [r12, #2680]
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
	ldr r7, [r12, #2684]
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
	ldr r7, [r12, #2688]
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
	ldr r7, [r12, #2692]
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
	ldr r7, [r12, #2696]
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
	ldr r7, [r12, #2700]
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
	ldr r7, [r12, #2704]
	ldr r8, [r12, #112]
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
	ldr r7, [r12, #2708]
	ldr r8, [r12, #116]
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
	ldr r7, [r12, #2712]
	ldr r8, [r12, #120]
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
	ldr r7, [r12, #2716]
	ldr r8, [r12, #124]
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
	ldr r7, [r12, #2720]
	ldr r8, [r12, #128]
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
	ldr r7, [r12, #2724]
	ldr r8, [r12, #132]
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
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	mov r10, lr
	mov r0, r12
	movw r1, #2512
	movw r2, #2440
	movw r3, #2872
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2584
	movw r2, #2656
	movw r3, #2872
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2728
	movw r2, #2584
	movw r3, #2584
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3016
	movw r2, #2512
	movw r3, #2512
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3088
	movw r2, #3016
	movw r3, #2512
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3016
	movw r2, #496
	movw r3, #2512
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2800
	movw r2, #3088
	movw r3, #3016
	bl {vg_p521_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3088
	movw r2, #2800
	movw r3, #2944
	bl {vg_p521_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3016
	movw r2, #2728
	movw r3, #3088
	bl {vg_p521_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #3016]
	ldr r4, [r12, #3020]
	orr r5, r5, r4
	ldr r4, [r12, #3024]
	orr r5, r5, r4
	ldr r4, [r12, #3028]
	orr r5, r5, r4
	ldr r4, [r12, #3032]
	orr r5, r5, r4
	ldr r4, [r12, #3036]
	orr r5, r5, r4
	ldr r4, [r12, #3040]
	orr r5, r5, r4
	ldr r4, [r12, #3044]
	orr r5, r5, r4
	ldr r4, [r12, #3048]
	orr r5, r5, r4
	ldr r4, [r12, #3052]
	orr r5, r5, r4
	ldr r4, [r12, #3056]
	orr r5, r5, r4
	ldr r4, [r12, #3060]
	orr r5, r5, r4
	ldr r4, [r12, #3064]
	orr r5, r5, r4
	ldr r4, [r12, #3068]
	orr r5, r5, r4
	ldr r4, [r12, #3072]
	orr r5, r5, r4
	ldr r4, [r12, #3076]
	orr r5, r5, r4
	ldr r4, [r12, #3080]
	orr r5, r5, r4
	ldr r4, [r12, #3084]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	mov r4, #0
	sub r5, r4, r5
	sub r5, r5, #1
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	ldr r10, [r12, #3232]
	ldr r4, [r12, #640]
	ldr r5, [r12, #2512]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2800]
	ldr r4, [r12, #644]
	ldr r5, [r12, #2516]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2804]
	ldr r4, [r12, #648]
	ldr r5, [r12, #2520]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2808]
	ldr r4, [r12, #652]
	ldr r5, [r12, #2524]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2812]
	ldr r4, [r12, #656]
	ldr r5, [r12, #2528]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2816]
	ldr r4, [r12, #660]
	ldr r5, [r12, #2532]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2820]
	ldr r4, [r12, #664]
	ldr r5, [r12, #2536]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2824]
	ldr r4, [r12, #668]
	ldr r5, [r12, #2540]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2828]
	ldr r4, [r12, #672]
	ldr r5, [r12, #2544]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2832]
	ldr r4, [r12, #676]
	ldr r5, [r12, #2548]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2836]
	ldr r4, [r12, #680]
	ldr r5, [r12, #2552]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2840]
	ldr r4, [r12, #684]
	ldr r5, [r12, #2556]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2844]
	ldr r4, [r12, #688]
	ldr r5, [r12, #2560]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2848]
	ldr r4, [r12, #692]
	ldr r5, [r12, #2564]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2852]
	ldr r4, [r12, #696]
	ldr r5, [r12, #2568]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2856]
	ldr r4, [r12, #700]
	ldr r5, [r12, #2572]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2860]
	ldr r4, [r12, #704]
	ldr r5, [r12, #2576]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2864]
	ldr r4, [r12, #708]
	ldr r5, [r12, #2580]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2868]
	ldr r4, [r12, #712]
	ldr r5, [r12, #2584]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3160]
	ldr r4, [r12, #716]
	ldr r5, [r12, #2588]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3164]
	ldr r4, [r12, #720]
	ldr r5, [r12, #2592]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3168]
	ldr r4, [r12, #724]
	ldr r5, [r12, #2596]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3172]
	ldr r4, [r12, #728]
	ldr r5, [r12, #2600]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3176]
	ldr r4, [r12, #732]
	ldr r5, [r12, #2604]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3180]
	ldr r4, [r12, #736]
	ldr r5, [r12, #2608]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3184]
	ldr r4, [r12, #740]
	ldr r5, [r12, #2612]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3188]
	ldr r4, [r12, #744]
	ldr r5, [r12, #2616]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3192]
	ldr r4, [r12, #748]
	ldr r5, [r12, #2620]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3196]
	ldr r4, [r12, #752]
	ldr r5, [r12, #2624]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3200]
	ldr r4, [r12, #756]
	ldr r5, [r12, #2628]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3204]
	ldr r4, [r12, #760]
	ldr r5, [r12, #2632]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3208]
	ldr r4, [r12, #764]
	ldr r5, [r12, #2636]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3212]
	ldr r4, [r12, #768]
	ldr r5, [r12, #2640]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3216]
	ldr r4, [r12, #772]
	ldr r5, [r12, #2644]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3220]
	ldr r4, [r12, #776]
	ldr r5, [r12, #2648]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3224]
	ldr r4, [r12, #780]
	ldr r5, [r12, #2652]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3228]
	ldr r10, [r12, #3232]
	ldr r4, [r12, #2656]
	and r4, r4, #1
	orr r4, r4, #2
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #2440]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #63]
	ldr r4, [r12, #2444]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #59]
	ldr r4, [r12, #2448]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #55]
	ldr r4, [r12, #2452]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #51]
	ldr r4, [r12, #2456]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #47]
	ldr r4, [r12, #2460]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #43]
	ldr r4, [r12, #2464]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #39]
	ldr r4, [r12, #2468]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #35]
	ldr r4, [r12, #2472]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #31]
	ldr r4, [r12, #2476]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #27]
	ldr r4, [r12, #2480]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #23]
	ldr r4, [r12, #2484]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #19]
	ldr r4, [r12, #2488]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #15]
	ldr r4, [r12, #2492]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #11]
	ldr r4, [r12, #2496]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #7]
	ldr r4, [r12, #2500]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #3]
	ldr r4, [r12, #2504]
	and r4, r4, r10
	lsr r5, r4, #8
	strb r5, [lr, #1]
	strb r4, [lr, #2]
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
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_ec_p521_decompress_public_key:
	mov r12, r2
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
	ldr r4, [r1, #62]
	rev r4, r4
	str r4, [r12, #2296]
	ldr r4, [r1, #58]
	rev r4, r4
	str r4, [r12, #2300]
	ldr r4, [r1, #54]
	rev r4, r4
	str r4, [r12, #2304]
	ldr r4, [r1, #50]
	rev r4, r4
	str r4, [r12, #2308]
	ldr r4, [r1, #46]
	rev r4, r4
	str r4, [r12, #2312]
	ldr r4, [r1, #42]
	rev r4, r4
	str r4, [r12, #2316]
	ldr r4, [r1, #38]
	rev r4, r4
	str r4, [r12, #2320]
	ldr r4, [r1, #34]
	rev r4, r4
	str r4, [r12, #2324]
	ldr r4, [r1, #30]
	rev r4, r4
	str r4, [r12, #2328]
	ldr r4, [r1, #26]
	rev r4, r4
	str r4, [r12, #2332]
	ldr r4, [r1, #22]
	rev r4, r4
	str r4, [r12, #2336]
	ldr r4, [r1, #18]
	rev r4, r4
	str r4, [r12, #2340]
	ldr r4, [r1, #14]
	rev r4, r4
	str r4, [r12, #2344]
	ldr r4, [r1, #10]
	rev r4, r4
	str r4, [r12, #2348]
	ldr r4, [r1, #6]
	rev r4, r4
	str r4, [r12, #2352]
	ldr r4, [r1, #2]
	rev r4, r4
	str r4, [r12, #2356]
	ldr r4, [r1, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2360]
	mov r4, #0
	str r4, [r12, #2364]
	ldr r4, [r1, #62]
	rev r4, r4
	str r4, [r12, #2368]
	ldr r4, [r1, #58]
	rev r4, r4
	str r4, [r12, #2372]
	ldr r4, [r1, #54]
	rev r4, r4
	str r4, [r12, #2376]
	ldr r4, [r1, #50]
	rev r4, r4
	str r4, [r12, #2380]
	ldr r4, [r1, #46]
	rev r4, r4
	str r4, [r12, #2384]
	ldr r4, [r1, #42]
	rev r4, r4
	str r4, [r12, #2388]
	ldr r4, [r1, #38]
	rev r4, r4
	str r4, [r12, #2392]
	ldr r4, [r1, #34]
	rev r4, r4
	str r4, [r12, #2396]
	ldr r4, [r1, #30]
	rev r4, r4
	str r4, [r12, #2400]
	ldr r4, [r1, #26]
	rev r4, r4
	str r4, [r12, #2404]
	ldr r4, [r1, #22]
	rev r4, r4
	str r4, [r12, #2408]
	ldr r4, [r1, #18]
	rev r4, r4
	str r4, [r12, #2412]
	ldr r4, [r1, #14]
	rev r4, r4
	str r4, [r12, #2416]
	ldr r4, [r1, #10]
	rev r4, r4
	str r4, [r12, #2420]
	ldr r4, [r1, #6]
	rev r4, r4
	str r4, [r12, #2424]
	ldr r4, [r1, #2]
	rev r4, r4
	str r4, [r12, #2428]
	ldr r4, [r1, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2432]
	mov r4, #0
	str r4, [r12, #2436]
	ldr r4, [r1, #62]
	rev r4, r4
	str r4, [r12, #2440]
	ldr r4, [r1, #58]
	rev r4, r4
	str r4, [r12, #2444]
	ldr r4, [r1, #54]
	rev r4, r4
	str r4, [r12, #2448]
	ldr r4, [r1, #50]
	rev r4, r4
	str r4, [r12, #2452]
	ldr r4, [r1, #46]
	rev r4, r4
	str r4, [r12, #2456]
	ldr r4, [r1, #42]
	rev r4, r4
	str r4, [r12, #2460]
	ldr r4, [r1, #38]
	rev r4, r4
	str r4, [r12, #2464]
	ldr r4, [r1, #34]
	rev r4, r4
	str r4, [r12, #2468]
	ldr r4, [r1, #30]
	rev r4, r4
	str r4, [r12, #2472]
	ldr r4, [r1, #26]
	rev r4, r4
	str r4, [r12, #2476]
	ldr r4, [r1, #22]
	rev r4, r4
	str r4, [r12, #2480]
	ldr r4, [r1, #18]
	rev r4, r4
	str r4, [r12, #2484]
	ldr r4, [r1, #14]
	rev r4, r4
	str r4, [r12, #2488]
	ldr r4, [r1, #10]
	rev r4, r4
	str r4, [r12, #2492]
	ldr r4, [r1, #6]
	rev r4, r4
	str r4, [r12, #2496]
	ldr r4, [r1, #2]
	rev r4, r4
	str r4, [r12, #2500]
	ldr r4, [r1, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2504]
	mov r4, #0
	str r4, [r12, #2508]
	movw r10, #:lower16:({VG_P521_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P521_FRAME_CONSTS}
2:
	add r10, pc
3:
	mov r9, r12
	mov r11, #17
20:
	sub r11, r11, #1
	ldr r4, [r10, #0]
	ldr r5, [r10, #4]
	str r4, [r9, #64]
	str r5, [r9, #68]
	ldr r4, [r10, #8]
	ldr r5, [r10, #12]
	str r4, [r9, #72]
	str r5, [r9, #76]
	ldr r4, [r10, #16]
	ldr r5, [r10, #20]
	str r4, [r9, #80]
	str r5, [r9, #84]
	ldr r4, [r10, #24]
	ldr r5, [r10, #28]
	str r4, [r9, #88]
	str r5, [r9, #92]
	ldr r4, [r10, #32]
	ldr r5, [r10, #36]
	str r4, [r9, #96]
	str r5, [r9, #100]
	ldr r4, [r10, #40]
	ldr r5, [r10, #44]
	str r4, [r9, #104]
	str r5, [r9, #108]
	ldr r4, [r10, #48]
	ldr r5, [r10, #52]
	str r4, [r9, #112]
	str r5, [r9, #116]
	ldr r4, [r10, #56]
	ldr r5, [r10, #60]
	str r4, [r9, #120]
	str r5, [r9, #124]
	ldr r4, [r10, #64]
	ldr r5, [r10, #68]
	str r4, [r9, #128]
	str r5, [r9, #132]
	add r10, r10, #72
	add r9, r9, #72
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #3232]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2872]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2876]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2880]
	movw r4, #16384
	movt r4, #0
	str r4, [r12, #2884]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2888]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2892]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2896]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2900]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2904]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2908]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2912]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2916]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2920]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2924]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2928]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2932]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2936]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2940]
	movw r4, #25479
	movt r4, #44632
	str r4, [r12, #2944]
	movw r4, #25935
	movt r4, #32788
	str r4, [r12, #2948]
	movw r4, #43039
	movt r4, #59957
	str r4, [r12, #2952]
	movw r4, #41615
	movt r4, #30967
	str r4, [r12, #2956]
	movw r4, #38426
	movt r4, #50206
	str r4, [r12, #2960]
	movw r4, #47599
	movt r4, #33690
	str r4, [r12, #2964]
	movw r4, #55519
	movt r4, #24221
	str r4, [r12, #2968]
	movw r4, #10592
	movt r4, #48523
	str r4, [r12, #2972]
	movw r4, #16201
	movt r4, #43254
	str r4, [r12, #2976]
	movw r4, #3228
	movt r4, #61611
	str r4, [r12, #2980]
	movw r4, #30852
	movt r4, #51399
	str r4, [r12, #2984]
	movw r4, #23108
	movt r4, #63964
	str r4, [r12, #2988]
	movw r4, #55690
	movt r4, #11724
	str r4, [r12, #2992]
	movw r4, #27961
	movt r4, #30545
	str r4, [r12, #2996]
	movw r4, #17056
	movt r4, #53339
	str r4, [r12, #3000]
	movw r4, #19728
	movt r4, #4041
	str r4, [r12, #3004]
	movw r4, #77
	movt r4, #0
	str r4, [r12, #3008]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3012]
	add r6, r1, #1
	ldr r4, [r6, #62]
	rev r4, r4
	str r4, [r12, #2440]
	ldr r4, [r6, #58]
	rev r4, r4
	str r4, [r12, #2444]
	ldr r4, [r6, #54]
	rev r4, r4
	str r4, [r12, #2448]
	ldr r4, [r6, #50]
	rev r4, r4
	str r4, [r12, #2452]
	ldr r4, [r6, #46]
	rev r4, r4
	str r4, [r12, #2456]
	ldr r4, [r6, #42]
	rev r4, r4
	str r4, [r12, #2460]
	ldr r4, [r6, #38]
	rev r4, r4
	str r4, [r12, #2464]
	ldr r4, [r6, #34]
	rev r4, r4
	str r4, [r12, #2468]
	ldr r4, [r6, #30]
	rev r4, r4
	str r4, [r12, #2472]
	ldr r4, [r6, #26]
	rev r4, r4
	str r4, [r12, #2476]
	ldr r4, [r6, #22]
	rev r4, r4
	str r4, [r12, #2480]
	ldr r4, [r6, #18]
	rev r4, r4
	str r4, [r12, #2484]
	ldr r4, [r6, #14]
	rev r4, r4
	str r4, [r12, #2488]
	ldr r4, [r6, #10]
	rev r4, r4
	str r4, [r12, #2492]
	ldr r4, [r6, #6]
	rev r4, r4
	str r4, [r12, #2496]
	ldr r4, [r6, #2]
	rev r4, r4
	str r4, [r12, #2500]
	ldr r4, [r6, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2504]
	mov r4, #0
	str r4, [r12, #2508]
	ldrb r4, [r1, #0]
	str r4, [r12, #2368]
	orr r4, r4, #1
	eor r4, r4, #3
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #2440]
	ldr r8, [r12, #64]
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
	ldr r7, [r12, #2444]
	ldr r8, [r12, #68]
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
	ldr r7, [r12, #2448]
	ldr r8, [r12, #72]
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
	ldr r7, [r12, #2452]
	ldr r8, [r12, #76]
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
	ldr r7, [r12, #2456]
	ldr r8, [r12, #80]
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
	ldr r7, [r12, #2460]
	ldr r8, [r12, #84]
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
	ldr r7, [r12, #2464]
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
	ldr r7, [r12, #2468]
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
	ldr r7, [r12, #2472]
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
	ldr r7, [r12, #2476]
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
	ldr r7, [r12, #2480]
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
	ldr r7, [r12, #2484]
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
	ldr r7, [r12, #2488]
	ldr r8, [r12, #112]
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
	ldr r7, [r12, #2492]
	ldr r8, [r12, #116]
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
	ldr r7, [r12, #2496]
	ldr r8, [r12, #120]
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
	ldr r7, [r12, #2500]
	ldr r8, [r12, #124]
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
	ldr r7, [r12, #2504]
	ldr r8, [r12, #128]
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
	ldr r7, [r12, #2508]
	ldr r8, [r12, #132]
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
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	mov r10, lr
	mov r0, r12
	movw r1, #2512
	movw r2, #2440
	movw r3, #2872
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3016
	movw r2, #2512
	movw r3, #2512
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3088
	movw r2, #3016
	movw r3, #2512
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3016
	movw r2, #496
	movw r3, #2512
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2800
	movw r2, #3088
	movw r3, #3016
	bl {vg_p521_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3088
	movw r2, #2800
	movw r3, #2944
	bl {vg_p521_add_mod_p}
	mov lr, r10
	movw r4, #0
	movt r4, #0
	str r4, [r12, #928]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #932]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #936]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #940]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #944]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #948]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #952]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #956]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #960]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #964]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #968]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #972]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #976]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #980]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #984]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #988]
	movw r4, #128
	movt r4, #0
	str r4, [r12, #992]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #996]
	mov r11, #72
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #928]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #1152]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #1153]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #1154]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #1155]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #1156]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #1157]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #1158]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #1159]
	cmp r11, #0
	bne 21b
	ldr r4, [r12, #424]
	str r4, [r12, #2152]
	ldr r4, [r12, #428]
	str r4, [r12, #2156]
	ldr r4, [r12, #432]
	str r4, [r12, #2160]
	ldr r4, [r12, #436]
	str r4, [r12, #2164]
	ldr r4, [r12, #440]
	str r4, [r12, #2168]
	ldr r4, [r12, #444]
	str r4, [r12, #2172]
	ldr r4, [r12, #448]
	str r4, [r12, #2176]
	ldr r4, [r12, #452]
	str r4, [r12, #2180]
	ldr r4, [r12, #456]
	str r4, [r12, #2184]
	ldr r4, [r12, #460]
	str r4, [r12, #2188]
	ldr r4, [r12, #464]
	str r4, [r12, #2192]
	ldr r4, [r12, #468]
	str r4, [r12, #2196]
	ldr r4, [r12, #472]
	str r4, [r12, #2200]
	ldr r4, [r12, #476]
	str r4, [r12, #2204]
	ldr r4, [r12, #480]
	str r4, [r12, #2208]
	ldr r4, [r12, #484]
	str r4, [r12, #2212]
	ldr r4, [r12, #488]
	str r4, [r12, #2216]
	ldr r4, [r12, #492]
	str r4, [r12, #2220]
	mov r11, #576
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #2152
	movw r2, #2152
	movw r3, #2152
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2224
	movw r2, #2152
	movw r3, #3088
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #1152]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #2152]
	ldr r5, [r12, #2224]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2152]
	ldr r4, [r12, #2156]
	ldr r5, [r12, #2228]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2156]
	ldr r4, [r12, #2160]
	ldr r5, [r12, #2232]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2160]
	ldr r4, [r12, #2164]
	ldr r5, [r12, #2236]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2164]
	ldr r4, [r12, #2168]
	ldr r5, [r12, #2240]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2168]
	ldr r4, [r12, #2172]
	ldr r5, [r12, #2244]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2172]
	ldr r4, [r12, #2176]
	ldr r5, [r12, #2248]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2176]
	ldr r4, [r12, #2180]
	ldr r5, [r12, #2252]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2180]
	ldr r4, [r12, #2184]
	ldr r5, [r12, #2256]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2184]
	ldr r4, [r12, #2188]
	ldr r5, [r12, #2260]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2188]
	ldr r4, [r12, #2192]
	ldr r5, [r12, #2264]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2192]
	ldr r4, [r12, #2196]
	ldr r5, [r12, #2268]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2196]
	ldr r4, [r12, #2200]
	ldr r5, [r12, #2272]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2200]
	ldr r4, [r12, #2204]
	ldr r5, [r12, #2276]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2204]
	ldr r4, [r12, #2208]
	ldr r5, [r12, #2280]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2208]
	ldr r4, [r12, #2212]
	ldr r5, [r12, #2284]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2212]
	ldr r4, [r12, #2216]
	ldr r5, [r12, #2288]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2216]
	ldr r4, [r12, #2220]
	ldr r5, [r12, #2292]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2220]
	cmp r11, #0
	bne 22b
	mov r10, lr
	mov r0, r12
	movw r1, #2656
	movw r2, #2152
	movw r3, #352
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2728
	movw r2, #280
	movw r3, #2656
	bl {vg_p521_sub_mod_p}
	mov lr, r10
	ldr r4, [r12, #2656]
	ldr r5, [r12, #2368]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	ldr r4, [r12, #2656]
	ldr r5, [r12, #2728]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2656]
	ldr r4, [r12, #2660]
	ldr r5, [r12, #2732]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2660]
	ldr r4, [r12, #2664]
	ldr r5, [r12, #2736]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2664]
	ldr r4, [r12, #2668]
	ldr r5, [r12, #2740]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2668]
	ldr r4, [r12, #2672]
	ldr r5, [r12, #2744]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2672]
	ldr r4, [r12, #2676]
	ldr r5, [r12, #2748]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2676]
	ldr r4, [r12, #2680]
	ldr r5, [r12, #2752]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2680]
	ldr r4, [r12, #2684]
	ldr r5, [r12, #2756]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2684]
	ldr r4, [r12, #2688]
	ldr r5, [r12, #2760]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2688]
	ldr r4, [r12, #2692]
	ldr r5, [r12, #2764]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2692]
	ldr r4, [r12, #2696]
	ldr r5, [r12, #2768]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2696]
	ldr r4, [r12, #2700]
	ldr r5, [r12, #2772]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2700]
	ldr r4, [r12, #2704]
	ldr r5, [r12, #2776]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2704]
	ldr r4, [r12, #2708]
	ldr r5, [r12, #2780]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2708]
	ldr r4, [r12, #2712]
	ldr r5, [r12, #2784]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2712]
	ldr r4, [r12, #2716]
	ldr r5, [r12, #2788]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2716]
	ldr r4, [r12, #2720]
	ldr r5, [r12, #2792]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2720]
	ldr r4, [r12, #2724]
	ldr r5, [r12, #2796]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2724]
	mov r10, lr
	mov r0, r12
	movw r1, #2584
	movw r2, #2656
	movw r3, #2872
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3016
	movw r2, #2584
	movw r3, #2584
	bl {vg_p521_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2800
	movw r2, #3016
	movw r3, #3088
	bl {vg_p521_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #2800]
	ldr r4, [r12, #2804]
	orr r5, r5, r4
	ldr r4, [r12, #2808]
	orr r5, r5, r4
	ldr r4, [r12, #2812]
	orr r5, r5, r4
	ldr r4, [r12, #2816]
	orr r5, r5, r4
	ldr r4, [r12, #2820]
	orr r5, r5, r4
	ldr r4, [r12, #2824]
	orr r5, r5, r4
	ldr r4, [r12, #2828]
	orr r5, r5, r4
	ldr r4, [r12, #2832]
	orr r5, r5, r4
	ldr r4, [r12, #2836]
	orr r5, r5, r4
	ldr r4, [r12, #2840]
	orr r5, r5, r4
	ldr r4, [r12, #2844]
	orr r5, r5, r4
	ldr r4, [r12, #2848]
	orr r5, r5, r4
	ldr r4, [r12, #2852]
	orr r5, r5, r4
	ldr r4, [r12, #2856]
	orr r5, r5, r4
	ldr r4, [r12, #2860]
	orr r5, r5, r4
	ldr r4, [r12, #2864]
	orr r5, r5, r4
	ldr r4, [r12, #2868]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	mov r4, #0
	sub r5, r4, r5
	sub r5, r5, #1
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	ldr r4, [r12, #2656]
	ldr r5, [r12, #2368]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	add r5, r10, #1
	mov r4, #0
	sub r5, r4, r5
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	ldr r10, [r12, #3232]
	mov r4, #4
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #2440]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #63]
	ldr r4, [r12, #2444]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #59]
	ldr r4, [r12, #2448]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #55]
	ldr r4, [r12, #2452]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #51]
	ldr r4, [r12, #2456]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #47]
	ldr r4, [r12, #2460]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #43]
	ldr r4, [r12, #2464]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #39]
	ldr r4, [r12, #2468]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #35]
	ldr r4, [r12, #2472]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #31]
	ldr r4, [r12, #2476]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #27]
	ldr r4, [r12, #2480]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #23]
	ldr r4, [r12, #2484]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #19]
	ldr r4, [r12, #2488]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #15]
	ldr r4, [r12, #2492]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #11]
	ldr r4, [r12, #2496]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #7]
	ldr r4, [r12, #2500]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #3]
	ldr r4, [r12, #2504]
	and r4, r4, r10
	lsr r5, r4, #8
	strb r5, [lr, #1]
	strb r4, [lr, #2]
	ldr r4, [r12, #2656]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #129]
	ldr r4, [r12, #2660]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #125]
	ldr r4, [r12, #2664]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #121]
	ldr r4, [r12, #2668]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #117]
	ldr r4, [r12, #2672]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #113]
	ldr r4, [r12, #2676]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #109]
	ldr r4, [r12, #2680]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #105]
	ldr r4, [r12, #2684]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #101]
	ldr r4, [r12, #2688]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #97]
	ldr r4, [r12, #2692]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #93]
	ldr r4, [r12, #2696]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #89]
	ldr r4, [r12, #2700]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #85]
	ldr r4, [r12, #2704]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #81]
	ldr r4, [r12, #2708]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #77]
	ldr r4, [r12, #2712]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #73]
	ldr r4, [r12, #2716]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #69]
	ldr r4, [r12, #2720]
	and r4, r4, r10
	lsr r5, r4, #8
	strb r5, [lr, #67]
	strb r4, [lr, #68]
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
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_ec_p521_compress_public_key_umaal:
	mov r12, r2
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
	ldr r4, [r1, #62]
	rev r4, r4
	str r4, [r12, #2296]
	ldr r4, [r1, #58]
	rev r4, r4
	str r4, [r12, #2300]
	ldr r4, [r1, #54]
	rev r4, r4
	str r4, [r12, #2304]
	ldr r4, [r1, #50]
	rev r4, r4
	str r4, [r12, #2308]
	ldr r4, [r1, #46]
	rev r4, r4
	str r4, [r12, #2312]
	ldr r4, [r1, #42]
	rev r4, r4
	str r4, [r12, #2316]
	ldr r4, [r1, #38]
	rev r4, r4
	str r4, [r12, #2320]
	ldr r4, [r1, #34]
	rev r4, r4
	str r4, [r12, #2324]
	ldr r4, [r1, #30]
	rev r4, r4
	str r4, [r12, #2328]
	ldr r4, [r1, #26]
	rev r4, r4
	str r4, [r12, #2332]
	ldr r4, [r1, #22]
	rev r4, r4
	str r4, [r12, #2336]
	ldr r4, [r1, #18]
	rev r4, r4
	str r4, [r12, #2340]
	ldr r4, [r1, #14]
	rev r4, r4
	str r4, [r12, #2344]
	ldr r4, [r1, #10]
	rev r4, r4
	str r4, [r12, #2348]
	ldr r4, [r1, #6]
	rev r4, r4
	str r4, [r12, #2352]
	ldr r4, [r1, #2]
	rev r4, r4
	str r4, [r12, #2356]
	ldr r4, [r1, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2360]
	mov r4, #0
	str r4, [r12, #2364]
	ldr r4, [r1, #62]
	rev r4, r4
	str r4, [r12, #2368]
	ldr r4, [r1, #58]
	rev r4, r4
	str r4, [r12, #2372]
	ldr r4, [r1, #54]
	rev r4, r4
	str r4, [r12, #2376]
	ldr r4, [r1, #50]
	rev r4, r4
	str r4, [r12, #2380]
	ldr r4, [r1, #46]
	rev r4, r4
	str r4, [r12, #2384]
	ldr r4, [r1, #42]
	rev r4, r4
	str r4, [r12, #2388]
	ldr r4, [r1, #38]
	rev r4, r4
	str r4, [r12, #2392]
	ldr r4, [r1, #34]
	rev r4, r4
	str r4, [r12, #2396]
	ldr r4, [r1, #30]
	rev r4, r4
	str r4, [r12, #2400]
	ldr r4, [r1, #26]
	rev r4, r4
	str r4, [r12, #2404]
	ldr r4, [r1, #22]
	rev r4, r4
	str r4, [r12, #2408]
	ldr r4, [r1, #18]
	rev r4, r4
	str r4, [r12, #2412]
	ldr r4, [r1, #14]
	rev r4, r4
	str r4, [r12, #2416]
	ldr r4, [r1, #10]
	rev r4, r4
	str r4, [r12, #2420]
	ldr r4, [r1, #6]
	rev r4, r4
	str r4, [r12, #2424]
	ldr r4, [r1, #2]
	rev r4, r4
	str r4, [r12, #2428]
	ldr r4, [r1, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2432]
	mov r4, #0
	str r4, [r12, #2436]
	ldr r4, [r1, #62]
	rev r4, r4
	str r4, [r12, #2440]
	ldr r4, [r1, #58]
	rev r4, r4
	str r4, [r12, #2444]
	ldr r4, [r1, #54]
	rev r4, r4
	str r4, [r12, #2448]
	ldr r4, [r1, #50]
	rev r4, r4
	str r4, [r12, #2452]
	ldr r4, [r1, #46]
	rev r4, r4
	str r4, [r12, #2456]
	ldr r4, [r1, #42]
	rev r4, r4
	str r4, [r12, #2460]
	ldr r4, [r1, #38]
	rev r4, r4
	str r4, [r12, #2464]
	ldr r4, [r1, #34]
	rev r4, r4
	str r4, [r12, #2468]
	ldr r4, [r1, #30]
	rev r4, r4
	str r4, [r12, #2472]
	ldr r4, [r1, #26]
	rev r4, r4
	str r4, [r12, #2476]
	ldr r4, [r1, #22]
	rev r4, r4
	str r4, [r12, #2480]
	ldr r4, [r1, #18]
	rev r4, r4
	str r4, [r12, #2484]
	ldr r4, [r1, #14]
	rev r4, r4
	str r4, [r12, #2488]
	ldr r4, [r1, #10]
	rev r4, r4
	str r4, [r12, #2492]
	ldr r4, [r1, #6]
	rev r4, r4
	str r4, [r12, #2496]
	ldr r4, [r1, #2]
	rev r4, r4
	str r4, [r12, #2500]
	ldr r4, [r1, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2504]
	mov r4, #0
	str r4, [r12, #2508]
	movw r10, #:lower16:({VG_P521_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P521_FRAME_CONSTS}
2:
	add r10, pc
3:
	mov r9, r12
	mov r11, #17
20:
	sub r11, r11, #1
	ldr r4, [r10, #0]
	ldr r5, [r10, #4]
	str r4, [r9, #64]
	str r5, [r9, #68]
	ldr r4, [r10, #8]
	ldr r5, [r10, #12]
	str r4, [r9, #72]
	str r5, [r9, #76]
	ldr r4, [r10, #16]
	ldr r5, [r10, #20]
	str r4, [r9, #80]
	str r5, [r9, #84]
	ldr r4, [r10, #24]
	ldr r5, [r10, #28]
	str r4, [r9, #88]
	str r5, [r9, #92]
	ldr r4, [r10, #32]
	ldr r5, [r10, #36]
	str r4, [r9, #96]
	str r5, [r9, #100]
	ldr r4, [r10, #40]
	ldr r5, [r10, #44]
	str r4, [r9, #104]
	str r5, [r9, #108]
	ldr r4, [r10, #48]
	ldr r5, [r10, #52]
	str r4, [r9, #112]
	str r5, [r9, #116]
	ldr r4, [r10, #56]
	ldr r5, [r10, #60]
	str r4, [r9, #120]
	str r5, [r9, #124]
	ldr r4, [r10, #64]
	ldr r5, [r10, #68]
	str r4, [r9, #128]
	str r5, [r9, #132]
	add r10, r10, #72
	add r9, r9, #72
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #3232]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2872]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2876]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2880]
	movw r4, #16384
	movt r4, #0
	str r4, [r12, #2884]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2888]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2892]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2896]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2900]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2904]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2908]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2912]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2916]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2920]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2924]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2928]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2932]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2936]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2940]
	movw r4, #25479
	movt r4, #44632
	str r4, [r12, #2944]
	movw r4, #25935
	movt r4, #32788
	str r4, [r12, #2948]
	movw r4, #43039
	movt r4, #59957
	str r4, [r12, #2952]
	movw r4, #41615
	movt r4, #30967
	str r4, [r12, #2956]
	movw r4, #38426
	movt r4, #50206
	str r4, [r12, #2960]
	movw r4, #47599
	movt r4, #33690
	str r4, [r12, #2964]
	movw r4, #55519
	movt r4, #24221
	str r4, [r12, #2968]
	movw r4, #10592
	movt r4, #48523
	str r4, [r12, #2972]
	movw r4, #16201
	movt r4, #43254
	str r4, [r12, #2976]
	movw r4, #3228
	movt r4, #61611
	str r4, [r12, #2980]
	movw r4, #30852
	movt r4, #51399
	str r4, [r12, #2984]
	movw r4, #23108
	movt r4, #63964
	str r4, [r12, #2988]
	movw r4, #55690
	movt r4, #11724
	str r4, [r12, #2992]
	movw r4, #27961
	movt r4, #30545
	str r4, [r12, #2996]
	movw r4, #17056
	movt r4, #53339
	str r4, [r12, #3000]
	movw r4, #19728
	movt r4, #4041
	str r4, [r12, #3004]
	movw r4, #77
	movt r4, #0
	str r4, [r12, #3008]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3012]
	add r6, r1, #1
	ldr r4, [r6, #62]
	rev r4, r4
	str r4, [r12, #2440]
	ldr r4, [r6, #58]
	rev r4, r4
	str r4, [r12, #2444]
	ldr r4, [r6, #54]
	rev r4, r4
	str r4, [r12, #2448]
	ldr r4, [r6, #50]
	rev r4, r4
	str r4, [r12, #2452]
	ldr r4, [r6, #46]
	rev r4, r4
	str r4, [r12, #2456]
	ldr r4, [r6, #42]
	rev r4, r4
	str r4, [r12, #2460]
	ldr r4, [r6, #38]
	rev r4, r4
	str r4, [r12, #2464]
	ldr r4, [r6, #34]
	rev r4, r4
	str r4, [r12, #2468]
	ldr r4, [r6, #30]
	rev r4, r4
	str r4, [r12, #2472]
	ldr r4, [r6, #26]
	rev r4, r4
	str r4, [r12, #2476]
	ldr r4, [r6, #22]
	rev r4, r4
	str r4, [r12, #2480]
	ldr r4, [r6, #18]
	rev r4, r4
	str r4, [r12, #2484]
	ldr r4, [r6, #14]
	rev r4, r4
	str r4, [r12, #2488]
	ldr r4, [r6, #10]
	rev r4, r4
	str r4, [r12, #2492]
	ldr r4, [r6, #6]
	rev r4, r4
	str r4, [r12, #2496]
	ldr r4, [r6, #2]
	rev r4, r4
	str r4, [r12, #2500]
	ldr r4, [r6, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2504]
	mov r4, #0
	str r4, [r12, #2508]
	add r6, r6, #66
	ldr r4, [r6, #62]
	rev r4, r4
	str r4, [r12, #2656]
	ldr r4, [r6, #58]
	rev r4, r4
	str r4, [r12, #2660]
	ldr r4, [r6, #54]
	rev r4, r4
	str r4, [r12, #2664]
	ldr r4, [r6, #50]
	rev r4, r4
	str r4, [r12, #2668]
	ldr r4, [r6, #46]
	rev r4, r4
	str r4, [r12, #2672]
	ldr r4, [r6, #42]
	rev r4, r4
	str r4, [r12, #2676]
	ldr r4, [r6, #38]
	rev r4, r4
	str r4, [r12, #2680]
	ldr r4, [r6, #34]
	rev r4, r4
	str r4, [r12, #2684]
	ldr r4, [r6, #30]
	rev r4, r4
	str r4, [r12, #2688]
	ldr r4, [r6, #26]
	rev r4, r4
	str r4, [r12, #2692]
	ldr r4, [r6, #22]
	rev r4, r4
	str r4, [r12, #2696]
	ldr r4, [r6, #18]
	rev r4, r4
	str r4, [r12, #2700]
	ldr r4, [r6, #14]
	rev r4, r4
	str r4, [r12, #2704]
	ldr r4, [r6, #10]
	rev r4, r4
	str r4, [r12, #2708]
	ldr r4, [r6, #6]
	rev r4, r4
	str r4, [r12, #2712]
	ldr r4, [r6, #2]
	rev r4, r4
	str r4, [r12, #2716]
	ldr r4, [r6, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2720]
	mov r4, #0
	str r4, [r12, #2724]
	ldrb r4, [r1, #0]
	eor r4, r4, #4
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #2440]
	ldr r8, [r12, #64]
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
	ldr r7, [r12, #2444]
	ldr r8, [r12, #68]
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
	ldr r7, [r12, #2448]
	ldr r8, [r12, #72]
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
	ldr r7, [r12, #2452]
	ldr r8, [r12, #76]
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
	ldr r7, [r12, #2456]
	ldr r8, [r12, #80]
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
	ldr r7, [r12, #2460]
	ldr r8, [r12, #84]
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
	ldr r7, [r12, #2464]
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
	ldr r7, [r12, #2468]
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
	ldr r7, [r12, #2472]
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
	ldr r7, [r12, #2476]
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
	ldr r7, [r12, #2480]
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
	ldr r7, [r12, #2484]
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
	ldr r7, [r12, #2488]
	ldr r8, [r12, #112]
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
	ldr r7, [r12, #2492]
	ldr r8, [r12, #116]
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
	ldr r7, [r12, #2496]
	ldr r8, [r12, #120]
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
	ldr r7, [r12, #2500]
	ldr r8, [r12, #124]
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
	ldr r7, [r12, #2504]
	ldr r8, [r12, #128]
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
	ldr r7, [r12, #2508]
	ldr r8, [r12, #132]
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
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #2656]
	ldr r8, [r12, #64]
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
	ldr r7, [r12, #2660]
	ldr r8, [r12, #68]
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
	ldr r7, [r12, #2664]
	ldr r8, [r12, #72]
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
	ldr r7, [r12, #2668]
	ldr r8, [r12, #76]
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
	ldr r7, [r12, #2672]
	ldr r8, [r12, #80]
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
	ldr r7, [r12, #2676]
	ldr r8, [r12, #84]
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
	ldr r7, [r12, #2680]
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
	ldr r7, [r12, #2684]
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
	ldr r7, [r12, #2688]
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
	ldr r7, [r12, #2692]
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
	ldr r7, [r12, #2696]
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
	ldr r7, [r12, #2700]
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
	ldr r7, [r12, #2704]
	ldr r8, [r12, #112]
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
	ldr r7, [r12, #2708]
	ldr r8, [r12, #116]
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
	ldr r7, [r12, #2712]
	ldr r8, [r12, #120]
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
	ldr r7, [r12, #2716]
	ldr r8, [r12, #124]
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
	ldr r7, [r12, #2720]
	ldr r8, [r12, #128]
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
	ldr r7, [r12, #2724]
	ldr r8, [r12, #132]
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
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	mov r10, lr
	mov r0, r12
	movw r1, #2512
	movw r2, #2440
	movw r3, #2872
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2584
	movw r2, #2656
	movw r3, #2872
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2728
	movw r2, #2584
	movw r3, #2584
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3016
	movw r2, #2512
	movw r3, #2512
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3088
	movw r2, #3016
	movw r3, #2512
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3016
	movw r2, #496
	movw r3, #2512
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2800
	movw r2, #3088
	movw r3, #3016
	bl {vg_p521_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3088
	movw r2, #2800
	movw r3, #2944
	bl {vg_p521_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3016
	movw r2, #2728
	movw r3, #3088
	bl {vg_p521_sub_mod_p_umaal}
	mov lr, r10
	ldr r5, [r12, #3016]
	ldr r4, [r12, #3020]
	orr r5, r5, r4
	ldr r4, [r12, #3024]
	orr r5, r5, r4
	ldr r4, [r12, #3028]
	orr r5, r5, r4
	ldr r4, [r12, #3032]
	orr r5, r5, r4
	ldr r4, [r12, #3036]
	orr r5, r5, r4
	ldr r4, [r12, #3040]
	orr r5, r5, r4
	ldr r4, [r12, #3044]
	orr r5, r5, r4
	ldr r4, [r12, #3048]
	orr r5, r5, r4
	ldr r4, [r12, #3052]
	orr r5, r5, r4
	ldr r4, [r12, #3056]
	orr r5, r5, r4
	ldr r4, [r12, #3060]
	orr r5, r5, r4
	ldr r4, [r12, #3064]
	orr r5, r5, r4
	ldr r4, [r12, #3068]
	orr r5, r5, r4
	ldr r4, [r12, #3072]
	orr r5, r5, r4
	ldr r4, [r12, #3076]
	orr r5, r5, r4
	ldr r4, [r12, #3080]
	orr r5, r5, r4
	ldr r4, [r12, #3084]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	mov r4, #0
	sub r5, r4, r5
	sub r5, r5, #1
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	ldr r10, [r12, #3232]
	ldr r4, [r12, #640]
	ldr r5, [r12, #2512]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2800]
	ldr r4, [r12, #644]
	ldr r5, [r12, #2516]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2804]
	ldr r4, [r12, #648]
	ldr r5, [r12, #2520]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2808]
	ldr r4, [r12, #652]
	ldr r5, [r12, #2524]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2812]
	ldr r4, [r12, #656]
	ldr r5, [r12, #2528]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2816]
	ldr r4, [r12, #660]
	ldr r5, [r12, #2532]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2820]
	ldr r4, [r12, #664]
	ldr r5, [r12, #2536]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2824]
	ldr r4, [r12, #668]
	ldr r5, [r12, #2540]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2828]
	ldr r4, [r12, #672]
	ldr r5, [r12, #2544]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2832]
	ldr r4, [r12, #676]
	ldr r5, [r12, #2548]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2836]
	ldr r4, [r12, #680]
	ldr r5, [r12, #2552]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2840]
	ldr r4, [r12, #684]
	ldr r5, [r12, #2556]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2844]
	ldr r4, [r12, #688]
	ldr r5, [r12, #2560]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2848]
	ldr r4, [r12, #692]
	ldr r5, [r12, #2564]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2852]
	ldr r4, [r12, #696]
	ldr r5, [r12, #2568]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2856]
	ldr r4, [r12, #700]
	ldr r5, [r12, #2572]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2860]
	ldr r4, [r12, #704]
	ldr r5, [r12, #2576]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2864]
	ldr r4, [r12, #708]
	ldr r5, [r12, #2580]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2868]
	ldr r4, [r12, #712]
	ldr r5, [r12, #2584]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3160]
	ldr r4, [r12, #716]
	ldr r5, [r12, #2588]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3164]
	ldr r4, [r12, #720]
	ldr r5, [r12, #2592]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3168]
	ldr r4, [r12, #724]
	ldr r5, [r12, #2596]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3172]
	ldr r4, [r12, #728]
	ldr r5, [r12, #2600]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3176]
	ldr r4, [r12, #732]
	ldr r5, [r12, #2604]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3180]
	ldr r4, [r12, #736]
	ldr r5, [r12, #2608]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3184]
	ldr r4, [r12, #740]
	ldr r5, [r12, #2612]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3188]
	ldr r4, [r12, #744]
	ldr r5, [r12, #2616]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3192]
	ldr r4, [r12, #748]
	ldr r5, [r12, #2620]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3196]
	ldr r4, [r12, #752]
	ldr r5, [r12, #2624]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3200]
	ldr r4, [r12, #756]
	ldr r5, [r12, #2628]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3204]
	ldr r4, [r12, #760]
	ldr r5, [r12, #2632]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3208]
	ldr r4, [r12, #764]
	ldr r5, [r12, #2636]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3212]
	ldr r4, [r12, #768]
	ldr r5, [r12, #2640]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3216]
	ldr r4, [r12, #772]
	ldr r5, [r12, #2644]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3220]
	ldr r4, [r12, #776]
	ldr r5, [r12, #2648]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3224]
	ldr r4, [r12, #780]
	ldr r5, [r12, #2652]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3228]
	ldr r10, [r12, #3232]
	ldr r4, [r12, #2656]
	and r4, r4, #1
	orr r4, r4, #2
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #2440]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #63]
	ldr r4, [r12, #2444]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #59]
	ldr r4, [r12, #2448]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #55]
	ldr r4, [r12, #2452]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #51]
	ldr r4, [r12, #2456]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #47]
	ldr r4, [r12, #2460]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #43]
	ldr r4, [r12, #2464]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #39]
	ldr r4, [r12, #2468]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #35]
	ldr r4, [r12, #2472]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #31]
	ldr r4, [r12, #2476]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #27]
	ldr r4, [r12, #2480]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #23]
	ldr r4, [r12, #2484]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #19]
	ldr r4, [r12, #2488]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #15]
	ldr r4, [r12, #2492]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #11]
	ldr r4, [r12, #2496]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #7]
	ldr r4, [r12, #2500]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #3]
	ldr r4, [r12, #2504]
	and r4, r4, r10
	lsr r5, r4, #8
	strb r5, [lr, #1]
	strb r4, [lr, #2]
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
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_ec_p521_decompress_public_key_umaal:
	mov r12, r2
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
	ldr r4, [r1, #62]
	rev r4, r4
	str r4, [r12, #2296]
	ldr r4, [r1, #58]
	rev r4, r4
	str r4, [r12, #2300]
	ldr r4, [r1, #54]
	rev r4, r4
	str r4, [r12, #2304]
	ldr r4, [r1, #50]
	rev r4, r4
	str r4, [r12, #2308]
	ldr r4, [r1, #46]
	rev r4, r4
	str r4, [r12, #2312]
	ldr r4, [r1, #42]
	rev r4, r4
	str r4, [r12, #2316]
	ldr r4, [r1, #38]
	rev r4, r4
	str r4, [r12, #2320]
	ldr r4, [r1, #34]
	rev r4, r4
	str r4, [r12, #2324]
	ldr r4, [r1, #30]
	rev r4, r4
	str r4, [r12, #2328]
	ldr r4, [r1, #26]
	rev r4, r4
	str r4, [r12, #2332]
	ldr r4, [r1, #22]
	rev r4, r4
	str r4, [r12, #2336]
	ldr r4, [r1, #18]
	rev r4, r4
	str r4, [r12, #2340]
	ldr r4, [r1, #14]
	rev r4, r4
	str r4, [r12, #2344]
	ldr r4, [r1, #10]
	rev r4, r4
	str r4, [r12, #2348]
	ldr r4, [r1, #6]
	rev r4, r4
	str r4, [r12, #2352]
	ldr r4, [r1, #2]
	rev r4, r4
	str r4, [r12, #2356]
	ldr r4, [r1, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2360]
	mov r4, #0
	str r4, [r12, #2364]
	ldr r4, [r1, #62]
	rev r4, r4
	str r4, [r12, #2368]
	ldr r4, [r1, #58]
	rev r4, r4
	str r4, [r12, #2372]
	ldr r4, [r1, #54]
	rev r4, r4
	str r4, [r12, #2376]
	ldr r4, [r1, #50]
	rev r4, r4
	str r4, [r12, #2380]
	ldr r4, [r1, #46]
	rev r4, r4
	str r4, [r12, #2384]
	ldr r4, [r1, #42]
	rev r4, r4
	str r4, [r12, #2388]
	ldr r4, [r1, #38]
	rev r4, r4
	str r4, [r12, #2392]
	ldr r4, [r1, #34]
	rev r4, r4
	str r4, [r12, #2396]
	ldr r4, [r1, #30]
	rev r4, r4
	str r4, [r12, #2400]
	ldr r4, [r1, #26]
	rev r4, r4
	str r4, [r12, #2404]
	ldr r4, [r1, #22]
	rev r4, r4
	str r4, [r12, #2408]
	ldr r4, [r1, #18]
	rev r4, r4
	str r4, [r12, #2412]
	ldr r4, [r1, #14]
	rev r4, r4
	str r4, [r12, #2416]
	ldr r4, [r1, #10]
	rev r4, r4
	str r4, [r12, #2420]
	ldr r4, [r1, #6]
	rev r4, r4
	str r4, [r12, #2424]
	ldr r4, [r1, #2]
	rev r4, r4
	str r4, [r12, #2428]
	ldr r4, [r1, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2432]
	mov r4, #0
	str r4, [r12, #2436]
	ldr r4, [r1, #62]
	rev r4, r4
	str r4, [r12, #2440]
	ldr r4, [r1, #58]
	rev r4, r4
	str r4, [r12, #2444]
	ldr r4, [r1, #54]
	rev r4, r4
	str r4, [r12, #2448]
	ldr r4, [r1, #50]
	rev r4, r4
	str r4, [r12, #2452]
	ldr r4, [r1, #46]
	rev r4, r4
	str r4, [r12, #2456]
	ldr r4, [r1, #42]
	rev r4, r4
	str r4, [r12, #2460]
	ldr r4, [r1, #38]
	rev r4, r4
	str r4, [r12, #2464]
	ldr r4, [r1, #34]
	rev r4, r4
	str r4, [r12, #2468]
	ldr r4, [r1, #30]
	rev r4, r4
	str r4, [r12, #2472]
	ldr r4, [r1, #26]
	rev r4, r4
	str r4, [r12, #2476]
	ldr r4, [r1, #22]
	rev r4, r4
	str r4, [r12, #2480]
	ldr r4, [r1, #18]
	rev r4, r4
	str r4, [r12, #2484]
	ldr r4, [r1, #14]
	rev r4, r4
	str r4, [r12, #2488]
	ldr r4, [r1, #10]
	rev r4, r4
	str r4, [r12, #2492]
	ldr r4, [r1, #6]
	rev r4, r4
	str r4, [r12, #2496]
	ldr r4, [r1, #2]
	rev r4, r4
	str r4, [r12, #2500]
	ldr r4, [r1, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2504]
	mov r4, #0
	str r4, [r12, #2508]
	movw r10, #:lower16:({VG_P521_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P521_FRAME_CONSTS}
2:
	add r10, pc
3:
	mov r9, r12
	mov r11, #17
20:
	sub r11, r11, #1
	ldr r4, [r10, #0]
	ldr r5, [r10, #4]
	str r4, [r9, #64]
	str r5, [r9, #68]
	ldr r4, [r10, #8]
	ldr r5, [r10, #12]
	str r4, [r9, #72]
	str r5, [r9, #76]
	ldr r4, [r10, #16]
	ldr r5, [r10, #20]
	str r4, [r9, #80]
	str r5, [r9, #84]
	ldr r4, [r10, #24]
	ldr r5, [r10, #28]
	str r4, [r9, #88]
	str r5, [r9, #92]
	ldr r4, [r10, #32]
	ldr r5, [r10, #36]
	str r4, [r9, #96]
	str r5, [r9, #100]
	ldr r4, [r10, #40]
	ldr r5, [r10, #44]
	str r4, [r9, #104]
	str r5, [r9, #108]
	ldr r4, [r10, #48]
	ldr r5, [r10, #52]
	str r4, [r9, #112]
	str r5, [r9, #116]
	ldr r4, [r10, #56]
	ldr r5, [r10, #60]
	str r4, [r9, #120]
	str r5, [r9, #124]
	ldr r4, [r10, #64]
	ldr r5, [r10, #68]
	str r4, [r9, #128]
	str r5, [r9, #132]
	add r10, r10, #72
	add r9, r9, #72
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #3232]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2872]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2876]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2880]
	movw r4, #16384
	movt r4, #0
	str r4, [r12, #2884]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2888]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2892]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2896]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2900]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2904]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2908]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2912]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2916]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2920]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2924]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2928]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2932]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2936]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #2940]
	movw r4, #25479
	movt r4, #44632
	str r4, [r12, #2944]
	movw r4, #25935
	movt r4, #32788
	str r4, [r12, #2948]
	movw r4, #43039
	movt r4, #59957
	str r4, [r12, #2952]
	movw r4, #41615
	movt r4, #30967
	str r4, [r12, #2956]
	movw r4, #38426
	movt r4, #50206
	str r4, [r12, #2960]
	movw r4, #47599
	movt r4, #33690
	str r4, [r12, #2964]
	movw r4, #55519
	movt r4, #24221
	str r4, [r12, #2968]
	movw r4, #10592
	movt r4, #48523
	str r4, [r12, #2972]
	movw r4, #16201
	movt r4, #43254
	str r4, [r12, #2976]
	movw r4, #3228
	movt r4, #61611
	str r4, [r12, #2980]
	movw r4, #30852
	movt r4, #51399
	str r4, [r12, #2984]
	movw r4, #23108
	movt r4, #63964
	str r4, [r12, #2988]
	movw r4, #55690
	movt r4, #11724
	str r4, [r12, #2992]
	movw r4, #27961
	movt r4, #30545
	str r4, [r12, #2996]
	movw r4, #17056
	movt r4, #53339
	str r4, [r12, #3000]
	movw r4, #19728
	movt r4, #4041
	str r4, [r12, #3004]
	movw r4, #77
	movt r4, #0
	str r4, [r12, #3008]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3012]
	add r6, r1, #1
	ldr r4, [r6, #62]
	rev r4, r4
	str r4, [r12, #2440]
	ldr r4, [r6, #58]
	rev r4, r4
	str r4, [r12, #2444]
	ldr r4, [r6, #54]
	rev r4, r4
	str r4, [r12, #2448]
	ldr r4, [r6, #50]
	rev r4, r4
	str r4, [r12, #2452]
	ldr r4, [r6, #46]
	rev r4, r4
	str r4, [r12, #2456]
	ldr r4, [r6, #42]
	rev r4, r4
	str r4, [r12, #2460]
	ldr r4, [r6, #38]
	rev r4, r4
	str r4, [r12, #2464]
	ldr r4, [r6, #34]
	rev r4, r4
	str r4, [r12, #2468]
	ldr r4, [r6, #30]
	rev r4, r4
	str r4, [r12, #2472]
	ldr r4, [r6, #26]
	rev r4, r4
	str r4, [r12, #2476]
	ldr r4, [r6, #22]
	rev r4, r4
	str r4, [r12, #2480]
	ldr r4, [r6, #18]
	rev r4, r4
	str r4, [r12, #2484]
	ldr r4, [r6, #14]
	rev r4, r4
	str r4, [r12, #2488]
	ldr r4, [r6, #10]
	rev r4, r4
	str r4, [r12, #2492]
	ldr r4, [r6, #6]
	rev r4, r4
	str r4, [r12, #2496]
	ldr r4, [r6, #2]
	rev r4, r4
	str r4, [r12, #2500]
	ldr r4, [r6, #0]
	rev r4, r4
	lsr r4, r4, #16
	str r4, [r12, #2504]
	mov r4, #0
	str r4, [r12, #2508]
	ldrb r4, [r1, #0]
	str r4, [r12, #2368]
	orr r4, r4, #1
	eor r4, r4, #3
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #2440]
	ldr r8, [r12, #64]
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
	ldr r7, [r12, #2444]
	ldr r8, [r12, #68]
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
	ldr r7, [r12, #2448]
	ldr r8, [r12, #72]
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
	ldr r7, [r12, #2452]
	ldr r8, [r12, #76]
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
	ldr r7, [r12, #2456]
	ldr r8, [r12, #80]
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
	ldr r7, [r12, #2460]
	ldr r8, [r12, #84]
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
	ldr r7, [r12, #2464]
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
	ldr r7, [r12, #2468]
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
	ldr r7, [r12, #2472]
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
	ldr r7, [r12, #2476]
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
	ldr r7, [r12, #2480]
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
	ldr r7, [r12, #2484]
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
	ldr r7, [r12, #2488]
	ldr r8, [r12, #112]
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
	ldr r7, [r12, #2492]
	ldr r8, [r12, #116]
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
	ldr r7, [r12, #2496]
	ldr r8, [r12, #120]
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
	ldr r7, [r12, #2500]
	ldr r8, [r12, #124]
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
	ldr r7, [r12, #2504]
	ldr r8, [r12, #128]
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
	ldr r7, [r12, #2508]
	ldr r8, [r12, #132]
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
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	mov r10, lr
	mov r0, r12
	movw r1, #2512
	movw r2, #2440
	movw r3, #2872
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3016
	movw r2, #2512
	movw r3, #2512
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3088
	movw r2, #3016
	movw r3, #2512
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3016
	movw r2, #496
	movw r3, #2512
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2800
	movw r2, #3088
	movw r3, #3016
	bl {vg_p521_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3088
	movw r2, #2800
	movw r3, #2944
	bl {vg_p521_add_mod_p_umaal}
	mov lr, r10
	movw r4, #0
	movt r4, #0
	str r4, [r12, #928]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #932]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #936]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #940]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #944]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #948]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #952]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #956]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #960]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #964]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #968]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #972]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #976]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #980]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #984]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #988]
	movw r4, #128
	movt r4, #0
	str r4, [r12, #992]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #996]
	mov r11, #72
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #928]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #1152]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #1153]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #1154]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #1155]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #1156]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #1157]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #1158]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #1159]
	cmp r11, #0
	bne 21b
	ldr r4, [r12, #424]
	str r4, [r12, #2152]
	ldr r4, [r12, #428]
	str r4, [r12, #2156]
	ldr r4, [r12, #432]
	str r4, [r12, #2160]
	ldr r4, [r12, #436]
	str r4, [r12, #2164]
	ldr r4, [r12, #440]
	str r4, [r12, #2168]
	ldr r4, [r12, #444]
	str r4, [r12, #2172]
	ldr r4, [r12, #448]
	str r4, [r12, #2176]
	ldr r4, [r12, #452]
	str r4, [r12, #2180]
	ldr r4, [r12, #456]
	str r4, [r12, #2184]
	ldr r4, [r12, #460]
	str r4, [r12, #2188]
	ldr r4, [r12, #464]
	str r4, [r12, #2192]
	ldr r4, [r12, #468]
	str r4, [r12, #2196]
	ldr r4, [r12, #472]
	str r4, [r12, #2200]
	ldr r4, [r12, #476]
	str r4, [r12, #2204]
	ldr r4, [r12, #480]
	str r4, [r12, #2208]
	ldr r4, [r12, #484]
	str r4, [r12, #2212]
	ldr r4, [r12, #488]
	str r4, [r12, #2216]
	ldr r4, [r12, #492]
	str r4, [r12, #2220]
	mov r11, #576
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #2152
	movw r2, #2152
	movw r3, #2152
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2224
	movw r2, #2152
	movw r3, #3088
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #1152]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #2152]
	ldr r5, [r12, #2224]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2152]
	ldr r4, [r12, #2156]
	ldr r5, [r12, #2228]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2156]
	ldr r4, [r12, #2160]
	ldr r5, [r12, #2232]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2160]
	ldr r4, [r12, #2164]
	ldr r5, [r12, #2236]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2164]
	ldr r4, [r12, #2168]
	ldr r5, [r12, #2240]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2168]
	ldr r4, [r12, #2172]
	ldr r5, [r12, #2244]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2172]
	ldr r4, [r12, #2176]
	ldr r5, [r12, #2248]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2176]
	ldr r4, [r12, #2180]
	ldr r5, [r12, #2252]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2180]
	ldr r4, [r12, #2184]
	ldr r5, [r12, #2256]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2184]
	ldr r4, [r12, #2188]
	ldr r5, [r12, #2260]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2188]
	ldr r4, [r12, #2192]
	ldr r5, [r12, #2264]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2192]
	ldr r4, [r12, #2196]
	ldr r5, [r12, #2268]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2196]
	ldr r4, [r12, #2200]
	ldr r5, [r12, #2272]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2200]
	ldr r4, [r12, #2204]
	ldr r5, [r12, #2276]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2204]
	ldr r4, [r12, #2208]
	ldr r5, [r12, #2280]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2208]
	ldr r4, [r12, #2212]
	ldr r5, [r12, #2284]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2212]
	ldr r4, [r12, #2216]
	ldr r5, [r12, #2288]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2216]
	ldr r4, [r12, #2220]
	ldr r5, [r12, #2292]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2220]
	cmp r11, #0
	bne 22b
	mov r10, lr
	mov r0, r12
	movw r1, #2656
	movw r2, #2152
	movw r3, #352
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2728
	movw r2, #280
	movw r3, #2656
	bl {vg_p521_sub_mod_p_umaal}
	mov lr, r10
	ldr r4, [r12, #2656]
	ldr r5, [r12, #2368]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	ldr r4, [r12, #2656]
	ldr r5, [r12, #2728]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2656]
	ldr r4, [r12, #2660]
	ldr r5, [r12, #2732]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2660]
	ldr r4, [r12, #2664]
	ldr r5, [r12, #2736]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2664]
	ldr r4, [r12, #2668]
	ldr r5, [r12, #2740]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2668]
	ldr r4, [r12, #2672]
	ldr r5, [r12, #2744]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2672]
	ldr r4, [r12, #2676]
	ldr r5, [r12, #2748]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2676]
	ldr r4, [r12, #2680]
	ldr r5, [r12, #2752]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2680]
	ldr r4, [r12, #2684]
	ldr r5, [r12, #2756]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2684]
	ldr r4, [r12, #2688]
	ldr r5, [r12, #2760]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2688]
	ldr r4, [r12, #2692]
	ldr r5, [r12, #2764]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2692]
	ldr r4, [r12, #2696]
	ldr r5, [r12, #2768]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2696]
	ldr r4, [r12, #2700]
	ldr r5, [r12, #2772]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2700]
	ldr r4, [r12, #2704]
	ldr r5, [r12, #2776]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2704]
	ldr r4, [r12, #2708]
	ldr r5, [r12, #2780]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2708]
	ldr r4, [r12, #2712]
	ldr r5, [r12, #2784]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2712]
	ldr r4, [r12, #2716]
	ldr r5, [r12, #2788]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2716]
	ldr r4, [r12, #2720]
	ldr r5, [r12, #2792]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2720]
	ldr r4, [r12, #2724]
	ldr r5, [r12, #2796]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2724]
	mov r10, lr
	mov r0, r12
	movw r1, #2584
	movw r2, #2656
	movw r3, #2872
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #3016
	movw r2, #2584
	movw r3, #2584
	bl {vg_p521_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2800
	movw r2, #3016
	movw r3, #3088
	bl {vg_p521_sub_mod_p_umaal}
	mov lr, r10
	ldr r5, [r12, #2800]
	ldr r4, [r12, #2804]
	orr r5, r5, r4
	ldr r4, [r12, #2808]
	orr r5, r5, r4
	ldr r4, [r12, #2812]
	orr r5, r5, r4
	ldr r4, [r12, #2816]
	orr r5, r5, r4
	ldr r4, [r12, #2820]
	orr r5, r5, r4
	ldr r4, [r12, #2824]
	orr r5, r5, r4
	ldr r4, [r12, #2828]
	orr r5, r5, r4
	ldr r4, [r12, #2832]
	orr r5, r5, r4
	ldr r4, [r12, #2836]
	orr r5, r5, r4
	ldr r4, [r12, #2840]
	orr r5, r5, r4
	ldr r4, [r12, #2844]
	orr r5, r5, r4
	ldr r4, [r12, #2848]
	orr r5, r5, r4
	ldr r4, [r12, #2852]
	orr r5, r5, r4
	ldr r4, [r12, #2856]
	orr r5, r5, r4
	ldr r4, [r12, #2860]
	orr r5, r5, r4
	ldr r4, [r12, #2864]
	orr r5, r5, r4
	ldr r4, [r12, #2868]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	mov r4, #0
	sub r5, r4, r5
	sub r5, r5, #1
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	ldr r4, [r12, #2656]
	ldr r5, [r12, #2368]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	add r5, r10, #1
	mov r4, #0
	sub r5, r4, r5
	ldr r4, [r12, #3232]
	and r4, r4, r5
	str r4, [r12, #3232]
	ldr r10, [r12, #3232]
	mov r4, #4
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #2440]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #63]
	ldr r4, [r12, #2444]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #59]
	ldr r4, [r12, #2448]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #55]
	ldr r4, [r12, #2452]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #51]
	ldr r4, [r12, #2456]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #47]
	ldr r4, [r12, #2460]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #43]
	ldr r4, [r12, #2464]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #39]
	ldr r4, [r12, #2468]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #35]
	ldr r4, [r12, #2472]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #31]
	ldr r4, [r12, #2476]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #27]
	ldr r4, [r12, #2480]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #23]
	ldr r4, [r12, #2484]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #19]
	ldr r4, [r12, #2488]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #15]
	ldr r4, [r12, #2492]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #11]
	ldr r4, [r12, #2496]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #7]
	ldr r4, [r12, #2500]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #3]
	ldr r4, [r12, #2504]
	and r4, r4, r10
	lsr r5, r4, #8
	strb r5, [lr, #1]
	strb r4, [lr, #2]
	ldr r4, [r12, #2656]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #129]
	ldr r4, [r12, #2660]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #125]
	ldr r4, [r12, #2664]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #121]
	ldr r4, [r12, #2668]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #117]
	ldr r4, [r12, #2672]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #113]
	ldr r4, [r12, #2676]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #109]
	ldr r4, [r12, #2680]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #105]
	ldr r4, [r12, #2684]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #101]
	ldr r4, [r12, #2688]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #97]
	ldr r4, [r12, #2692]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #93]
	ldr r4, [r12, #2696]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #89]
	ldr r4, [r12, #2700]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #85]
	ldr r4, [r12, #2704]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #81]
	ldr r4, [r12, #2708]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #77]
	ldr r4, [r12, #2712]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #73]
	ldr r4, [r12, #2716]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #69]
	ldr r4, [r12, #2720]
	and r4, r4, r10
	lsr r5, r4, #8
	strb r5, [lr, #67]
	strb r4, [lr, #68]
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
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
