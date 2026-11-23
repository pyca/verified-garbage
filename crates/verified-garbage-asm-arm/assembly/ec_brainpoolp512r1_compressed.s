// The functions of `src/ec_brainpoolp512r1_compressed.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp512r1_compress_public_key:
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
	ldr r4, [r1, #60]
	rev r4, r4
	str r4, [r12, #2048]
	ldr r4, [r1, #56]
	rev r4, r4
	str r4, [r12, #2052]
	ldr r4, [r1, #52]
	rev r4, r4
	str r4, [r12, #2056]
	ldr r4, [r1, #48]
	rev r4, r4
	str r4, [r12, #2060]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #2064]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #2068]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #2072]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #2076]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #2080]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #2084]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #2088]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #2092]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #2096]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #2100]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #2104]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #2108]
	ldr r4, [r1, #60]
	rev r4, r4
	str r4, [r12, #2112]
	ldr r4, [r1, #56]
	rev r4, r4
	str r4, [r12, #2116]
	ldr r4, [r1, #52]
	rev r4, r4
	str r4, [r12, #2120]
	ldr r4, [r1, #48]
	rev r4, r4
	str r4, [r12, #2124]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #2128]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #2132]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #2136]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #2140]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #2144]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #2148]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #2152]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #2156]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #2160]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #2164]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #2168]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #2172]
	ldr r4, [r1, #60]
	rev r4, r4
	str r4, [r12, #2176]
	ldr r4, [r1, #56]
	rev r4, r4
	str r4, [r12, #2180]
	ldr r4, [r1, #52]
	rev r4, r4
	str r4, [r12, #2184]
	ldr r4, [r1, #48]
	rev r4, r4
	str r4, [r12, #2188]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #2192]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #2196]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #2200]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #2204]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #2208]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #2212]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #2216]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #2220]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #2224]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #2228]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #2232]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #2236]
	movw r10, #:lower16:({VG_BRAINPOOLP512R1_FRAME_CONSTS}
	movt r10, #:upper16:({VG_BRAINPOOLP512R1_FRAME_CONSTS}
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
	add r10, r10, #64
	add r9, r9, #64
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #2880]
	movw r4, #61957
	movt r4, #24920
	str r4, [r12, #2560]
	movw r4, #5194
	movt r4, #18861
	str r4, [r12, #2564]
	movw r4, #30981
	movt r4, #10005
	str r4, [r12, #2568]
	movw r4, #45360
	movt r4, #31039
	str r4, [r12, #2572]
	movw r4, #65491
	movt r4, #36954
	str r4, [r12, #2576]
	movw r4, #63932
	movt r4, #21431
	str r4, [r12, #2580]
	movw r4, #18981
	movt r4, #33617
	str r4, [r12, #2584]
	movw r4, #39543
	movt r4, #57537
	str r4, [r12, #2588]
	movw r4, #32855
	movt r4, #54665
	str r4, [r12, #2592]
	movw r4, #28632
	movt r4, #6472
	str r4, [r12, #2596]
	movw r4, #65411
	movt r4, #54315
	str r4, [r12, #2600]
	movw r4, #43615
	movt r4, #41325
	str r4, [r12, #2604]
	movw r4, #61132
	movt r4, #8278
	str r4, [r12, #2608]
	movw r4, #6464
	movt r4, #8238
	str r4, [r12, #2612]
	movw r4, #25680
	movt r4, #43519
	str r4, [r12, #2616]
	movw r4, #40197
	movt r4, #15436
	str r4, [r12, #2620]
	movw r4, #10804
	movt r4, #8425
	str r4, [r12, #2624]
	movw r4, #33686
	movt r4, #20606
	str r4, [r12, #2628]
	movw r4, #23092
	movt r4, #58766
	str r4, [r12, #2632]
	movw r4, #25543
	movt r4, #155
	str r4, [r12, #2636]
	movw r4, #9386
	movt r4, #11655
	str r4, [r12, #2640]
	movw r4, #42070
	movt r4, #57707
	str r4, [r12, #2644]
	movw r4, #48642
	movt r4, #39031
	str r4, [r12, #2648]
	movw r4, #12520
	movt r4, #51006
	str r4, [r12, #2652]
	movw r4, #9267
	movt r4, #65058
	str r4, [r12, #2656]
	movw r4, #3171
	movt r4, #38880
	str r4, [r12, #2660]
	movw r4, #55325
	movt r4, #27927
	str r4, [r12, #2664]
	movw r4, #22444
	movt r4, #52186
	str r4, [r12, #2668]
	movw r4, #43682
	movt r4, #2997
	str r4, [r12, #2672]
	movw r4, #4773
	movt r4, #25635
	str r4, [r12, #2676]
	movw r4, #36519
	movt r4, #18206
	str r4, [r12, #2680]
	movw r4, #43956
	movt r4, #27210
	str r4, [r12, #2684]
	add r6, r1, #1
	ldr r4, [r6, #60]
	rev r4, r4
	str r4, [r12, #2176]
	ldr r4, [r6, #56]
	rev r4, r4
	str r4, [r12, #2180]
	ldr r4, [r6, #52]
	rev r4, r4
	str r4, [r12, #2184]
	ldr r4, [r6, #48]
	rev r4, r4
	str r4, [r12, #2188]
	ldr r4, [r6, #44]
	rev r4, r4
	str r4, [r12, #2192]
	ldr r4, [r6, #40]
	rev r4, r4
	str r4, [r12, #2196]
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #2200]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #2204]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #2208]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #2212]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #2216]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #2220]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #2224]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #2228]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #2232]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #2236]
	add r6, r6, #64
	ldr r4, [r6, #60]
	rev r4, r4
	str r4, [r12, #2368]
	ldr r4, [r6, #56]
	rev r4, r4
	str r4, [r12, #2372]
	ldr r4, [r6, #52]
	rev r4, r4
	str r4, [r12, #2376]
	ldr r4, [r6, #48]
	rev r4, r4
	str r4, [r12, #2380]
	ldr r4, [r6, #44]
	rev r4, r4
	str r4, [r12, #2384]
	ldr r4, [r6, #40]
	rev r4, r4
	str r4, [r12, #2388]
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #2392]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #2396]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #2400]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #2404]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #2408]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #2412]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #2416]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #2420]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #2424]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #2428]
	ldrb r4, [r1, #0]
	eor r4, r4, #4
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #2176]
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
	ldr r7, [r12, #2180]
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
	ldr r7, [r12, #2184]
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
	ldr r7, [r12, #2188]
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
	ldr r7, [r12, #2192]
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
	ldr r7, [r12, #2196]
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
	ldr r7, [r12, #2200]
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
	ldr r7, [r12, #2204]
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
	ldr r7, [r12, #2208]
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
	ldr r7, [r12, #2212]
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
	ldr r7, [r12, #2216]
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
	ldr r7, [r12, #2220]
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
	ldr r7, [r12, #2224]
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
	ldr r7, [r12, #2228]
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
	ldr r7, [r12, #2232]
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
	ldr r7, [r12, #2236]
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
	sub r5, r3, #1
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #2368]
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
	ldr r7, [r12, #2372]
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
	ldr r7, [r12, #2376]
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
	ldr r7, [r12, #2380]
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
	ldr r7, [r12, #2384]
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
	ldr r7, [r12, #2388]
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
	ldr r7, [r12, #2392]
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
	ldr r7, [r12, #2396]
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
	ldr r7, [r12, #2400]
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
	ldr r7, [r12, #2404]
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
	ldr r7, [r12, #2408]
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
	ldr r7, [r12, #2412]
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
	ldr r7, [r12, #2416]
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
	ldr r7, [r12, #2420]
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
	ldr r7, [r12, #2424]
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
	ldr r7, [r12, #2428]
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
	sub r5, r3, #1
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	mov r10, lr
	mov r0, r12
	movw r1, #2240
	movw r2, #2176
	movw r3, #2560
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2304
	movw r2, #2368
	movw r3, #2560
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2432
	movw r2, #2304
	movw r3, #2304
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2688
	movw r2, #2240
	movw r3, #2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2752
	movw r2, #2688
	movw r3, #2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2688
	movw r2, #448
	movw r3, #2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2496
	movw r2, #2752
	movw r3, #2688
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2752
	movw r2, #2496
	movw r3, #2624
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2688
	movw r2, #2432
	movw r3, #2752
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #2688]
	ldr r4, [r12, #2692]
	orr r5, r5, r4
	ldr r4, [r12, #2696]
	orr r5, r5, r4
	ldr r4, [r12, #2700]
	orr r5, r5, r4
	ldr r4, [r12, #2704]
	orr r5, r5, r4
	ldr r4, [r12, #2708]
	orr r5, r5, r4
	ldr r4, [r12, #2712]
	orr r5, r5, r4
	ldr r4, [r12, #2716]
	orr r5, r5, r4
	ldr r4, [r12, #2720]
	orr r5, r5, r4
	ldr r4, [r12, #2724]
	orr r5, r5, r4
	ldr r4, [r12, #2728]
	orr r5, r5, r4
	ldr r4, [r12, #2732]
	orr r5, r5, r4
	ldr r4, [r12, #2736]
	orr r5, r5, r4
	ldr r4, [r12, #2740]
	orr r5, r5, r4
	ldr r4, [r12, #2744]
	orr r5, r5, r4
	ldr r4, [r12, #2748]
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
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	ldr r10, [r12, #2880]
	ldr r4, [r12, #576]
	ldr r5, [r12, #2240]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2496]
	ldr r4, [r12, #580]
	ldr r5, [r12, #2244]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2500]
	ldr r4, [r12, #584]
	ldr r5, [r12, #2248]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2504]
	ldr r4, [r12, #588]
	ldr r5, [r12, #2252]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2508]
	ldr r4, [r12, #592]
	ldr r5, [r12, #2256]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2512]
	ldr r4, [r12, #596]
	ldr r5, [r12, #2260]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2516]
	ldr r4, [r12, #600]
	ldr r5, [r12, #2264]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2520]
	ldr r4, [r12, #604]
	ldr r5, [r12, #2268]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2524]
	ldr r4, [r12, #608]
	ldr r5, [r12, #2272]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2528]
	ldr r4, [r12, #612]
	ldr r5, [r12, #2276]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2532]
	ldr r4, [r12, #616]
	ldr r5, [r12, #2280]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2536]
	ldr r4, [r12, #620]
	ldr r5, [r12, #2284]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2540]
	ldr r4, [r12, #624]
	ldr r5, [r12, #2288]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2544]
	ldr r4, [r12, #628]
	ldr r5, [r12, #2292]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2548]
	ldr r4, [r12, #632]
	ldr r5, [r12, #2296]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2552]
	ldr r4, [r12, #636]
	ldr r5, [r12, #2300]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2556]
	ldr r4, [r12, #640]
	ldr r5, [r12, #2304]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2816]
	ldr r4, [r12, #644]
	ldr r5, [r12, #2308]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2820]
	ldr r4, [r12, #648]
	ldr r5, [r12, #2312]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2824]
	ldr r4, [r12, #652]
	ldr r5, [r12, #2316]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2828]
	ldr r4, [r12, #656]
	ldr r5, [r12, #2320]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2832]
	ldr r4, [r12, #660]
	ldr r5, [r12, #2324]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2836]
	ldr r4, [r12, #664]
	ldr r5, [r12, #2328]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2840]
	ldr r4, [r12, #668]
	ldr r5, [r12, #2332]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2844]
	ldr r4, [r12, #672]
	ldr r5, [r12, #2336]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2848]
	ldr r4, [r12, #676]
	ldr r5, [r12, #2340]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2852]
	ldr r4, [r12, #680]
	ldr r5, [r12, #2344]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2856]
	ldr r4, [r12, #684]
	ldr r5, [r12, #2348]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2860]
	ldr r4, [r12, #688]
	ldr r5, [r12, #2352]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2864]
	ldr r4, [r12, #692]
	ldr r5, [r12, #2356]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2868]
	ldr r4, [r12, #696]
	ldr r5, [r12, #2360]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2872]
	ldr r4, [r12, #700]
	ldr r5, [r12, #2364]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2876]
	ldr r10, [r12, #2880]
	ldr r4, [r12, #2368]
	and r4, r4, #1
	orr r4, r4, #2
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #2176]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #61]
	ldr r4, [r12, #2180]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #57]
	ldr r4, [r12, #2184]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #53]
	ldr r4, [r12, #2188]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #49]
	ldr r4, [r12, #2192]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #2196]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
	ldr r4, [r12, #2200]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #2204]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #2208]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #2212]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #2216]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #2220]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #2224]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #2228]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #2232]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #2236]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
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

vg_ec_brainpoolp512r1_decompress_public_key:
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
	ldr r4, [r1, #60]
	rev r4, r4
	str r4, [r12, #2048]
	ldr r4, [r1, #56]
	rev r4, r4
	str r4, [r12, #2052]
	ldr r4, [r1, #52]
	rev r4, r4
	str r4, [r12, #2056]
	ldr r4, [r1, #48]
	rev r4, r4
	str r4, [r12, #2060]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #2064]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #2068]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #2072]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #2076]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #2080]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #2084]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #2088]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #2092]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #2096]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #2100]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #2104]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #2108]
	ldr r4, [r1, #60]
	rev r4, r4
	str r4, [r12, #2112]
	ldr r4, [r1, #56]
	rev r4, r4
	str r4, [r12, #2116]
	ldr r4, [r1, #52]
	rev r4, r4
	str r4, [r12, #2120]
	ldr r4, [r1, #48]
	rev r4, r4
	str r4, [r12, #2124]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #2128]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #2132]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #2136]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #2140]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #2144]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #2148]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #2152]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #2156]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #2160]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #2164]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #2168]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #2172]
	ldr r4, [r1, #60]
	rev r4, r4
	str r4, [r12, #2176]
	ldr r4, [r1, #56]
	rev r4, r4
	str r4, [r12, #2180]
	ldr r4, [r1, #52]
	rev r4, r4
	str r4, [r12, #2184]
	ldr r4, [r1, #48]
	rev r4, r4
	str r4, [r12, #2188]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #2192]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #2196]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #2200]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #2204]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #2208]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #2212]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #2216]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #2220]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #2224]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #2228]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #2232]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #2236]
	movw r10, #:lower16:({VG_BRAINPOOLP512R1_FRAME_CONSTS}
	movt r10, #:upper16:({VG_BRAINPOOLP512R1_FRAME_CONSTS}
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
	add r10, r10, #64
	add r9, r9, #64
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #2880]
	movw r4, #61957
	movt r4, #24920
	str r4, [r12, #2560]
	movw r4, #5194
	movt r4, #18861
	str r4, [r12, #2564]
	movw r4, #30981
	movt r4, #10005
	str r4, [r12, #2568]
	movw r4, #45360
	movt r4, #31039
	str r4, [r12, #2572]
	movw r4, #65491
	movt r4, #36954
	str r4, [r12, #2576]
	movw r4, #63932
	movt r4, #21431
	str r4, [r12, #2580]
	movw r4, #18981
	movt r4, #33617
	str r4, [r12, #2584]
	movw r4, #39543
	movt r4, #57537
	str r4, [r12, #2588]
	movw r4, #32855
	movt r4, #54665
	str r4, [r12, #2592]
	movw r4, #28632
	movt r4, #6472
	str r4, [r12, #2596]
	movw r4, #65411
	movt r4, #54315
	str r4, [r12, #2600]
	movw r4, #43615
	movt r4, #41325
	str r4, [r12, #2604]
	movw r4, #61132
	movt r4, #8278
	str r4, [r12, #2608]
	movw r4, #6464
	movt r4, #8238
	str r4, [r12, #2612]
	movw r4, #25680
	movt r4, #43519
	str r4, [r12, #2616]
	movw r4, #40197
	movt r4, #15436
	str r4, [r12, #2620]
	movw r4, #10804
	movt r4, #8425
	str r4, [r12, #2624]
	movw r4, #33686
	movt r4, #20606
	str r4, [r12, #2628]
	movw r4, #23092
	movt r4, #58766
	str r4, [r12, #2632]
	movw r4, #25543
	movt r4, #155
	str r4, [r12, #2636]
	movw r4, #9386
	movt r4, #11655
	str r4, [r12, #2640]
	movw r4, #42070
	movt r4, #57707
	str r4, [r12, #2644]
	movw r4, #48642
	movt r4, #39031
	str r4, [r12, #2648]
	movw r4, #12520
	movt r4, #51006
	str r4, [r12, #2652]
	movw r4, #9267
	movt r4, #65058
	str r4, [r12, #2656]
	movw r4, #3171
	movt r4, #38880
	str r4, [r12, #2660]
	movw r4, #55325
	movt r4, #27927
	str r4, [r12, #2664]
	movw r4, #22444
	movt r4, #52186
	str r4, [r12, #2668]
	movw r4, #43682
	movt r4, #2997
	str r4, [r12, #2672]
	movw r4, #4773
	movt r4, #25635
	str r4, [r12, #2676]
	movw r4, #36519
	movt r4, #18206
	str r4, [r12, #2680]
	movw r4, #43956
	movt r4, #27210
	str r4, [r12, #2684]
	add r6, r1, #1
	ldr r4, [r6, #60]
	rev r4, r4
	str r4, [r12, #2176]
	ldr r4, [r6, #56]
	rev r4, r4
	str r4, [r12, #2180]
	ldr r4, [r6, #52]
	rev r4, r4
	str r4, [r12, #2184]
	ldr r4, [r6, #48]
	rev r4, r4
	str r4, [r12, #2188]
	ldr r4, [r6, #44]
	rev r4, r4
	str r4, [r12, #2192]
	ldr r4, [r6, #40]
	rev r4, r4
	str r4, [r12, #2196]
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #2200]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #2204]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #2208]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #2212]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #2216]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #2220]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #2224]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #2228]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #2232]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #2236]
	ldrb r4, [r1, #0]
	str r4, [r12, #2112]
	orr r4, r4, #1
	eor r4, r4, #3
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #2176]
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
	ldr r7, [r12, #2180]
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
	ldr r7, [r12, #2184]
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
	ldr r7, [r12, #2188]
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
	ldr r7, [r12, #2192]
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
	ldr r7, [r12, #2196]
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
	ldr r7, [r12, #2200]
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
	ldr r7, [r12, #2204]
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
	ldr r7, [r12, #2208]
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
	ldr r7, [r12, #2212]
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
	ldr r7, [r12, #2216]
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
	ldr r7, [r12, #2220]
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
	ldr r7, [r12, #2224]
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
	ldr r7, [r12, #2228]
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
	ldr r7, [r12, #2232]
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
	ldr r7, [r12, #2236]
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
	sub r5, r3, #1
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	mov r10, lr
	mov r0, r12
	movw r1, #2240
	movw r2, #2176
	movw r3, #2560
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2688
	movw r2, #2240
	movw r3, #2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2752
	movw r2, #2688
	movw r3, #2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2688
	movw r2, #448
	movw r3, #2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2496
	movw r2, #2752
	movw r3, #2688
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2752
	movw r2, #2496
	movw r3, #2624
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	movw r4, #37437
	movt r4, #38414
	str r4, [r12, #832]
	movw r4, #38933
	movt r4, #18986
	str r4, [r12, #836]
	movw r4, #45473
	movt r4, #52064
	str r4, [r12, #840]
	movw r4, #32715
	movt r4, #35360
	str r4, [r12, #844]
	movw r4, #57401
	movt r4, #47528
	str r4, [r12, #848]
	movw r4, #26698
	movt r4, #43955
	str r4, [r12, #852]
	movw r4, #39440
	movt r4, #9969
	str r4, [r12, #856]
	movw r4, #26304
	movt r4, #24403
	str r4, [r12, #860]
	movw r4, #49692
	movt r4, #39948
	str r4, [r12, #864]
	movw r4, #59186
	movt r4, #46488
	str r4, [r12, #868]
	movw r4, #29827
	movt r4, #60658
	str r4, [r12, #872]
	movw r4, #9068
	movt r4, #62156
	str r4, [r12, #876]
	movw r4, #32513
	movt r4, #36082
	str r4, [r12, #880]
	movw r4, #14763
	movt r4, #53237
	str r4, [r12, #884]
	movw r4, #28962
	movt r4, #14074
	str r4, [r12, #888]
	movw r4, #26478
	movt r4, #10935
	str r4, [r12, #892]
	mov r11, #64
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #832]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #1024]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #1025]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #1026]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #1027]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #1028]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #1029]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #1030]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #1031]
	cmp r11, #0
	bne 21b
	ldr r4, [r12, #384]
	str r4, [r12, #1920]
	ldr r4, [r12, #388]
	str r4, [r12, #1924]
	ldr r4, [r12, #392]
	str r4, [r12, #1928]
	ldr r4, [r12, #396]
	str r4, [r12, #1932]
	ldr r4, [r12, #400]
	str r4, [r12, #1936]
	ldr r4, [r12, #404]
	str r4, [r12, #1940]
	ldr r4, [r12, #408]
	str r4, [r12, #1944]
	ldr r4, [r12, #412]
	str r4, [r12, #1948]
	ldr r4, [r12, #416]
	str r4, [r12, #1952]
	ldr r4, [r12, #420]
	str r4, [r12, #1956]
	ldr r4, [r12, #424]
	str r4, [r12, #1960]
	ldr r4, [r12, #428]
	str r4, [r12, #1964]
	ldr r4, [r12, #432]
	str r4, [r12, #1968]
	ldr r4, [r12, #436]
	str r4, [r12, #1972]
	ldr r4, [r12, #440]
	str r4, [r12, #1976]
	ldr r4, [r12, #444]
	str r4, [r12, #1980]
	mov r11, #512
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #1920
	movw r2, #1920
	movw r3, #1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1984
	movw r2, #1920
	movw r3, #2752
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #1024]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #1920]
	ldr r5, [r12, #1984]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1920]
	ldr r4, [r12, #1924]
	ldr r5, [r12, #1988]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1924]
	ldr r4, [r12, #1928]
	ldr r5, [r12, #1992]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1928]
	ldr r4, [r12, #1932]
	ldr r5, [r12, #1996]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1932]
	ldr r4, [r12, #1936]
	ldr r5, [r12, #2000]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1936]
	ldr r4, [r12, #1940]
	ldr r5, [r12, #2004]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1940]
	ldr r4, [r12, #1944]
	ldr r5, [r12, #2008]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1944]
	ldr r4, [r12, #1948]
	ldr r5, [r12, #2012]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1948]
	ldr r4, [r12, #1952]
	ldr r5, [r12, #2016]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1952]
	ldr r4, [r12, #1956]
	ldr r5, [r12, #2020]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1956]
	ldr r4, [r12, #1960]
	ldr r5, [r12, #2024]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1960]
	ldr r4, [r12, #1964]
	ldr r5, [r12, #2028]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1964]
	ldr r4, [r12, #1968]
	ldr r5, [r12, #2032]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1968]
	ldr r4, [r12, #1972]
	ldr r5, [r12, #2036]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1972]
	ldr r4, [r12, #1976]
	ldr r5, [r12, #2040]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1976]
	ldr r4, [r12, #1980]
	ldr r5, [r12, #2044]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1980]
	cmp r11, #0
	bne 22b
	mov r10, lr
	mov r0, r12
	movw r1, #2368
	movw r2, #1920
	movw r3, #320
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2432
	movw r2, #256
	movw r3, #2368
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	ldr r4, [r12, #2368]
	ldr r5, [r12, #2112]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	ldr r4, [r12, #2368]
	ldr r5, [r12, #2432]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2368]
	ldr r4, [r12, #2372]
	ldr r5, [r12, #2436]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2372]
	ldr r4, [r12, #2376]
	ldr r5, [r12, #2440]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2376]
	ldr r4, [r12, #2380]
	ldr r5, [r12, #2444]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2380]
	ldr r4, [r12, #2384]
	ldr r5, [r12, #2448]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2384]
	ldr r4, [r12, #2388]
	ldr r5, [r12, #2452]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2388]
	ldr r4, [r12, #2392]
	ldr r5, [r12, #2456]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2392]
	ldr r4, [r12, #2396]
	ldr r5, [r12, #2460]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2396]
	ldr r4, [r12, #2400]
	ldr r5, [r12, #2464]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2400]
	ldr r4, [r12, #2404]
	ldr r5, [r12, #2468]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2404]
	ldr r4, [r12, #2408]
	ldr r5, [r12, #2472]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2408]
	ldr r4, [r12, #2412]
	ldr r5, [r12, #2476]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2412]
	ldr r4, [r12, #2416]
	ldr r5, [r12, #2480]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2416]
	ldr r4, [r12, #2420]
	ldr r5, [r12, #2484]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2420]
	ldr r4, [r12, #2424]
	ldr r5, [r12, #2488]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2424]
	ldr r4, [r12, #2428]
	ldr r5, [r12, #2492]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2428]
	mov r10, lr
	mov r0, r12
	movw r1, #2304
	movw r2, #2368
	movw r3, #2560
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2688
	movw r2, #2304
	movw r3, #2304
	bl {vg_brainpoolp512r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2496
	movw r2, #2688
	movw r3, #2752
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #2496]
	ldr r4, [r12, #2500]
	orr r5, r5, r4
	ldr r4, [r12, #2504]
	orr r5, r5, r4
	ldr r4, [r12, #2508]
	orr r5, r5, r4
	ldr r4, [r12, #2512]
	orr r5, r5, r4
	ldr r4, [r12, #2516]
	orr r5, r5, r4
	ldr r4, [r12, #2520]
	orr r5, r5, r4
	ldr r4, [r12, #2524]
	orr r5, r5, r4
	ldr r4, [r12, #2528]
	orr r5, r5, r4
	ldr r4, [r12, #2532]
	orr r5, r5, r4
	ldr r4, [r12, #2536]
	orr r5, r5, r4
	ldr r4, [r12, #2540]
	orr r5, r5, r4
	ldr r4, [r12, #2544]
	orr r5, r5, r4
	ldr r4, [r12, #2548]
	orr r5, r5, r4
	ldr r4, [r12, #2552]
	orr r5, r5, r4
	ldr r4, [r12, #2556]
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
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	ldr r4, [r12, #2368]
	ldr r5, [r12, #2112]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	add r5, r10, #1
	mov r4, #0
	sub r5, r4, r5
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	ldr r10, [r12, #2880]
	mov r4, #4
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #2176]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #61]
	ldr r4, [r12, #2180]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #57]
	ldr r4, [r12, #2184]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #53]
	ldr r4, [r12, #2188]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #49]
	ldr r4, [r12, #2192]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #2196]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
	ldr r4, [r12, #2200]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #2204]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #2208]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #2212]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #2216]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #2220]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #2224]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #2228]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #2232]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #2236]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
	ldr r4, [r12, #2368]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #125]
	ldr r4, [r12, #2372]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #121]
	ldr r4, [r12, #2376]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #117]
	ldr r4, [r12, #2380]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #113]
	ldr r4, [r12, #2384]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #109]
	ldr r4, [r12, #2388]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #105]
	ldr r4, [r12, #2392]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #101]
	ldr r4, [r12, #2396]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #97]
	ldr r4, [r12, #2400]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #93]
	ldr r4, [r12, #2404]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #89]
	ldr r4, [r12, #2408]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #85]
	ldr r4, [r12, #2412]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #81]
	ldr r4, [r12, #2416]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #77]
	ldr r4, [r12, #2420]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #73]
	ldr r4, [r12, #2424]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #69]
	ldr r4, [r12, #2428]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #65]
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

vg_ec_brainpoolp512r1_compress_public_key_umaal:
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
	ldr r4, [r1, #60]
	rev r4, r4
	str r4, [r12, #2048]
	ldr r4, [r1, #56]
	rev r4, r4
	str r4, [r12, #2052]
	ldr r4, [r1, #52]
	rev r4, r4
	str r4, [r12, #2056]
	ldr r4, [r1, #48]
	rev r4, r4
	str r4, [r12, #2060]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #2064]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #2068]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #2072]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #2076]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #2080]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #2084]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #2088]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #2092]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #2096]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #2100]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #2104]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #2108]
	ldr r4, [r1, #60]
	rev r4, r4
	str r4, [r12, #2112]
	ldr r4, [r1, #56]
	rev r4, r4
	str r4, [r12, #2116]
	ldr r4, [r1, #52]
	rev r4, r4
	str r4, [r12, #2120]
	ldr r4, [r1, #48]
	rev r4, r4
	str r4, [r12, #2124]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #2128]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #2132]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #2136]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #2140]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #2144]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #2148]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #2152]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #2156]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #2160]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #2164]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #2168]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #2172]
	ldr r4, [r1, #60]
	rev r4, r4
	str r4, [r12, #2176]
	ldr r4, [r1, #56]
	rev r4, r4
	str r4, [r12, #2180]
	ldr r4, [r1, #52]
	rev r4, r4
	str r4, [r12, #2184]
	ldr r4, [r1, #48]
	rev r4, r4
	str r4, [r12, #2188]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #2192]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #2196]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #2200]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #2204]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #2208]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #2212]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #2216]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #2220]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #2224]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #2228]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #2232]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #2236]
	movw r10, #:lower16:({VG_BRAINPOOLP512R1_FRAME_CONSTS}
	movt r10, #:upper16:({VG_BRAINPOOLP512R1_FRAME_CONSTS}
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
	add r10, r10, #64
	add r9, r9, #64
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #2880]
	movw r4, #61957
	movt r4, #24920
	str r4, [r12, #2560]
	movw r4, #5194
	movt r4, #18861
	str r4, [r12, #2564]
	movw r4, #30981
	movt r4, #10005
	str r4, [r12, #2568]
	movw r4, #45360
	movt r4, #31039
	str r4, [r12, #2572]
	movw r4, #65491
	movt r4, #36954
	str r4, [r12, #2576]
	movw r4, #63932
	movt r4, #21431
	str r4, [r12, #2580]
	movw r4, #18981
	movt r4, #33617
	str r4, [r12, #2584]
	movw r4, #39543
	movt r4, #57537
	str r4, [r12, #2588]
	movw r4, #32855
	movt r4, #54665
	str r4, [r12, #2592]
	movw r4, #28632
	movt r4, #6472
	str r4, [r12, #2596]
	movw r4, #65411
	movt r4, #54315
	str r4, [r12, #2600]
	movw r4, #43615
	movt r4, #41325
	str r4, [r12, #2604]
	movw r4, #61132
	movt r4, #8278
	str r4, [r12, #2608]
	movw r4, #6464
	movt r4, #8238
	str r4, [r12, #2612]
	movw r4, #25680
	movt r4, #43519
	str r4, [r12, #2616]
	movw r4, #40197
	movt r4, #15436
	str r4, [r12, #2620]
	movw r4, #10804
	movt r4, #8425
	str r4, [r12, #2624]
	movw r4, #33686
	movt r4, #20606
	str r4, [r12, #2628]
	movw r4, #23092
	movt r4, #58766
	str r4, [r12, #2632]
	movw r4, #25543
	movt r4, #155
	str r4, [r12, #2636]
	movw r4, #9386
	movt r4, #11655
	str r4, [r12, #2640]
	movw r4, #42070
	movt r4, #57707
	str r4, [r12, #2644]
	movw r4, #48642
	movt r4, #39031
	str r4, [r12, #2648]
	movw r4, #12520
	movt r4, #51006
	str r4, [r12, #2652]
	movw r4, #9267
	movt r4, #65058
	str r4, [r12, #2656]
	movw r4, #3171
	movt r4, #38880
	str r4, [r12, #2660]
	movw r4, #55325
	movt r4, #27927
	str r4, [r12, #2664]
	movw r4, #22444
	movt r4, #52186
	str r4, [r12, #2668]
	movw r4, #43682
	movt r4, #2997
	str r4, [r12, #2672]
	movw r4, #4773
	movt r4, #25635
	str r4, [r12, #2676]
	movw r4, #36519
	movt r4, #18206
	str r4, [r12, #2680]
	movw r4, #43956
	movt r4, #27210
	str r4, [r12, #2684]
	add r6, r1, #1
	ldr r4, [r6, #60]
	rev r4, r4
	str r4, [r12, #2176]
	ldr r4, [r6, #56]
	rev r4, r4
	str r4, [r12, #2180]
	ldr r4, [r6, #52]
	rev r4, r4
	str r4, [r12, #2184]
	ldr r4, [r6, #48]
	rev r4, r4
	str r4, [r12, #2188]
	ldr r4, [r6, #44]
	rev r4, r4
	str r4, [r12, #2192]
	ldr r4, [r6, #40]
	rev r4, r4
	str r4, [r12, #2196]
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #2200]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #2204]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #2208]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #2212]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #2216]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #2220]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #2224]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #2228]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #2232]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #2236]
	add r6, r6, #64
	ldr r4, [r6, #60]
	rev r4, r4
	str r4, [r12, #2368]
	ldr r4, [r6, #56]
	rev r4, r4
	str r4, [r12, #2372]
	ldr r4, [r6, #52]
	rev r4, r4
	str r4, [r12, #2376]
	ldr r4, [r6, #48]
	rev r4, r4
	str r4, [r12, #2380]
	ldr r4, [r6, #44]
	rev r4, r4
	str r4, [r12, #2384]
	ldr r4, [r6, #40]
	rev r4, r4
	str r4, [r12, #2388]
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #2392]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #2396]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #2400]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #2404]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #2408]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #2412]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #2416]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #2420]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #2424]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #2428]
	ldrb r4, [r1, #0]
	eor r4, r4, #4
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #2176]
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
	ldr r7, [r12, #2180]
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
	ldr r7, [r12, #2184]
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
	ldr r7, [r12, #2188]
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
	ldr r7, [r12, #2192]
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
	ldr r7, [r12, #2196]
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
	ldr r7, [r12, #2200]
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
	ldr r7, [r12, #2204]
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
	ldr r7, [r12, #2208]
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
	ldr r7, [r12, #2212]
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
	ldr r7, [r12, #2216]
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
	ldr r7, [r12, #2220]
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
	ldr r7, [r12, #2224]
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
	ldr r7, [r12, #2228]
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
	ldr r7, [r12, #2232]
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
	ldr r7, [r12, #2236]
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
	sub r5, r3, #1
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #2368]
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
	ldr r7, [r12, #2372]
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
	ldr r7, [r12, #2376]
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
	ldr r7, [r12, #2380]
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
	ldr r7, [r12, #2384]
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
	ldr r7, [r12, #2388]
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
	ldr r7, [r12, #2392]
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
	ldr r7, [r12, #2396]
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
	ldr r7, [r12, #2400]
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
	ldr r7, [r12, #2404]
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
	ldr r7, [r12, #2408]
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
	ldr r7, [r12, #2412]
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
	ldr r7, [r12, #2416]
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
	ldr r7, [r12, #2420]
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
	ldr r7, [r12, #2424]
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
	ldr r7, [r12, #2428]
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
	sub r5, r3, #1
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	mov r10, lr
	mov r0, r12
	movw r1, #2240
	movw r2, #2176
	movw r3, #2560
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2304
	movw r2, #2368
	movw r3, #2560
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2432
	movw r2, #2304
	movw r3, #2304
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2688
	movw r2, #2240
	movw r3, #2240
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2752
	movw r2, #2688
	movw r3, #2240
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2688
	movw r2, #448
	movw r3, #2240
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2496
	movw r2, #2752
	movw r3, #2688
	bl {vg_brainpoolp512r1_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2752
	movw r2, #2496
	movw r3, #2624
	bl {vg_brainpoolp512r1_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2688
	movw r2, #2432
	movw r3, #2752
	bl {vg_brainpoolp512r1_sub_mod_p_umaal}
	mov lr, r10
	ldr r5, [r12, #2688]
	ldr r4, [r12, #2692]
	orr r5, r5, r4
	ldr r4, [r12, #2696]
	orr r5, r5, r4
	ldr r4, [r12, #2700]
	orr r5, r5, r4
	ldr r4, [r12, #2704]
	orr r5, r5, r4
	ldr r4, [r12, #2708]
	orr r5, r5, r4
	ldr r4, [r12, #2712]
	orr r5, r5, r4
	ldr r4, [r12, #2716]
	orr r5, r5, r4
	ldr r4, [r12, #2720]
	orr r5, r5, r4
	ldr r4, [r12, #2724]
	orr r5, r5, r4
	ldr r4, [r12, #2728]
	orr r5, r5, r4
	ldr r4, [r12, #2732]
	orr r5, r5, r4
	ldr r4, [r12, #2736]
	orr r5, r5, r4
	ldr r4, [r12, #2740]
	orr r5, r5, r4
	ldr r4, [r12, #2744]
	orr r5, r5, r4
	ldr r4, [r12, #2748]
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
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	ldr r10, [r12, #2880]
	ldr r4, [r12, #576]
	ldr r5, [r12, #2240]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2496]
	ldr r4, [r12, #580]
	ldr r5, [r12, #2244]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2500]
	ldr r4, [r12, #584]
	ldr r5, [r12, #2248]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2504]
	ldr r4, [r12, #588]
	ldr r5, [r12, #2252]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2508]
	ldr r4, [r12, #592]
	ldr r5, [r12, #2256]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2512]
	ldr r4, [r12, #596]
	ldr r5, [r12, #2260]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2516]
	ldr r4, [r12, #600]
	ldr r5, [r12, #2264]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2520]
	ldr r4, [r12, #604]
	ldr r5, [r12, #2268]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2524]
	ldr r4, [r12, #608]
	ldr r5, [r12, #2272]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2528]
	ldr r4, [r12, #612]
	ldr r5, [r12, #2276]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2532]
	ldr r4, [r12, #616]
	ldr r5, [r12, #2280]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2536]
	ldr r4, [r12, #620]
	ldr r5, [r12, #2284]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2540]
	ldr r4, [r12, #624]
	ldr r5, [r12, #2288]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2544]
	ldr r4, [r12, #628]
	ldr r5, [r12, #2292]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2548]
	ldr r4, [r12, #632]
	ldr r5, [r12, #2296]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2552]
	ldr r4, [r12, #636]
	ldr r5, [r12, #2300]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2556]
	ldr r4, [r12, #640]
	ldr r5, [r12, #2304]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2816]
	ldr r4, [r12, #644]
	ldr r5, [r12, #2308]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2820]
	ldr r4, [r12, #648]
	ldr r5, [r12, #2312]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2824]
	ldr r4, [r12, #652]
	ldr r5, [r12, #2316]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2828]
	ldr r4, [r12, #656]
	ldr r5, [r12, #2320]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2832]
	ldr r4, [r12, #660]
	ldr r5, [r12, #2324]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2836]
	ldr r4, [r12, #664]
	ldr r5, [r12, #2328]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2840]
	ldr r4, [r12, #668]
	ldr r5, [r12, #2332]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2844]
	ldr r4, [r12, #672]
	ldr r5, [r12, #2336]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2848]
	ldr r4, [r12, #676]
	ldr r5, [r12, #2340]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2852]
	ldr r4, [r12, #680]
	ldr r5, [r12, #2344]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2856]
	ldr r4, [r12, #684]
	ldr r5, [r12, #2348]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2860]
	ldr r4, [r12, #688]
	ldr r5, [r12, #2352]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2864]
	ldr r4, [r12, #692]
	ldr r5, [r12, #2356]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2868]
	ldr r4, [r12, #696]
	ldr r5, [r12, #2360]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2872]
	ldr r4, [r12, #700]
	ldr r5, [r12, #2364]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2876]
	ldr r10, [r12, #2880]
	ldr r4, [r12, #2368]
	and r4, r4, #1
	orr r4, r4, #2
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #2176]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #61]
	ldr r4, [r12, #2180]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #57]
	ldr r4, [r12, #2184]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #53]
	ldr r4, [r12, #2188]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #49]
	ldr r4, [r12, #2192]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #2196]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
	ldr r4, [r12, #2200]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #2204]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #2208]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #2212]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #2216]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #2220]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #2224]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #2228]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #2232]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #2236]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
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

vg_ec_brainpoolp512r1_decompress_public_key_umaal:
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
	ldr r4, [r1, #60]
	rev r4, r4
	str r4, [r12, #2048]
	ldr r4, [r1, #56]
	rev r4, r4
	str r4, [r12, #2052]
	ldr r4, [r1, #52]
	rev r4, r4
	str r4, [r12, #2056]
	ldr r4, [r1, #48]
	rev r4, r4
	str r4, [r12, #2060]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #2064]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #2068]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #2072]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #2076]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #2080]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #2084]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #2088]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #2092]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #2096]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #2100]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #2104]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #2108]
	ldr r4, [r1, #60]
	rev r4, r4
	str r4, [r12, #2112]
	ldr r4, [r1, #56]
	rev r4, r4
	str r4, [r12, #2116]
	ldr r4, [r1, #52]
	rev r4, r4
	str r4, [r12, #2120]
	ldr r4, [r1, #48]
	rev r4, r4
	str r4, [r12, #2124]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #2128]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #2132]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #2136]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #2140]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #2144]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #2148]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #2152]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #2156]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #2160]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #2164]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #2168]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #2172]
	ldr r4, [r1, #60]
	rev r4, r4
	str r4, [r12, #2176]
	ldr r4, [r1, #56]
	rev r4, r4
	str r4, [r12, #2180]
	ldr r4, [r1, #52]
	rev r4, r4
	str r4, [r12, #2184]
	ldr r4, [r1, #48]
	rev r4, r4
	str r4, [r12, #2188]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #2192]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #2196]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #2200]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #2204]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #2208]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #2212]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #2216]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #2220]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #2224]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #2228]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #2232]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #2236]
	movw r10, #:lower16:({VG_BRAINPOOLP512R1_FRAME_CONSTS}
	movt r10, #:upper16:({VG_BRAINPOOLP512R1_FRAME_CONSTS}
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
	add r10, r10, #64
	add r9, r9, #64
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #2880]
	movw r4, #61957
	movt r4, #24920
	str r4, [r12, #2560]
	movw r4, #5194
	movt r4, #18861
	str r4, [r12, #2564]
	movw r4, #30981
	movt r4, #10005
	str r4, [r12, #2568]
	movw r4, #45360
	movt r4, #31039
	str r4, [r12, #2572]
	movw r4, #65491
	movt r4, #36954
	str r4, [r12, #2576]
	movw r4, #63932
	movt r4, #21431
	str r4, [r12, #2580]
	movw r4, #18981
	movt r4, #33617
	str r4, [r12, #2584]
	movw r4, #39543
	movt r4, #57537
	str r4, [r12, #2588]
	movw r4, #32855
	movt r4, #54665
	str r4, [r12, #2592]
	movw r4, #28632
	movt r4, #6472
	str r4, [r12, #2596]
	movw r4, #65411
	movt r4, #54315
	str r4, [r12, #2600]
	movw r4, #43615
	movt r4, #41325
	str r4, [r12, #2604]
	movw r4, #61132
	movt r4, #8278
	str r4, [r12, #2608]
	movw r4, #6464
	movt r4, #8238
	str r4, [r12, #2612]
	movw r4, #25680
	movt r4, #43519
	str r4, [r12, #2616]
	movw r4, #40197
	movt r4, #15436
	str r4, [r12, #2620]
	movw r4, #10804
	movt r4, #8425
	str r4, [r12, #2624]
	movw r4, #33686
	movt r4, #20606
	str r4, [r12, #2628]
	movw r4, #23092
	movt r4, #58766
	str r4, [r12, #2632]
	movw r4, #25543
	movt r4, #155
	str r4, [r12, #2636]
	movw r4, #9386
	movt r4, #11655
	str r4, [r12, #2640]
	movw r4, #42070
	movt r4, #57707
	str r4, [r12, #2644]
	movw r4, #48642
	movt r4, #39031
	str r4, [r12, #2648]
	movw r4, #12520
	movt r4, #51006
	str r4, [r12, #2652]
	movw r4, #9267
	movt r4, #65058
	str r4, [r12, #2656]
	movw r4, #3171
	movt r4, #38880
	str r4, [r12, #2660]
	movw r4, #55325
	movt r4, #27927
	str r4, [r12, #2664]
	movw r4, #22444
	movt r4, #52186
	str r4, [r12, #2668]
	movw r4, #43682
	movt r4, #2997
	str r4, [r12, #2672]
	movw r4, #4773
	movt r4, #25635
	str r4, [r12, #2676]
	movw r4, #36519
	movt r4, #18206
	str r4, [r12, #2680]
	movw r4, #43956
	movt r4, #27210
	str r4, [r12, #2684]
	add r6, r1, #1
	ldr r4, [r6, #60]
	rev r4, r4
	str r4, [r12, #2176]
	ldr r4, [r6, #56]
	rev r4, r4
	str r4, [r12, #2180]
	ldr r4, [r6, #52]
	rev r4, r4
	str r4, [r12, #2184]
	ldr r4, [r6, #48]
	rev r4, r4
	str r4, [r12, #2188]
	ldr r4, [r6, #44]
	rev r4, r4
	str r4, [r12, #2192]
	ldr r4, [r6, #40]
	rev r4, r4
	str r4, [r12, #2196]
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #2200]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #2204]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #2208]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #2212]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #2216]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #2220]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #2224]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #2228]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #2232]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #2236]
	ldrb r4, [r1, #0]
	str r4, [r12, #2112]
	orr r4, r4, #1
	eor r4, r4, #3
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #2176]
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
	ldr r7, [r12, #2180]
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
	ldr r7, [r12, #2184]
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
	ldr r7, [r12, #2188]
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
	ldr r7, [r12, #2192]
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
	ldr r7, [r12, #2196]
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
	ldr r7, [r12, #2200]
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
	ldr r7, [r12, #2204]
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
	ldr r7, [r12, #2208]
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
	ldr r7, [r12, #2212]
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
	ldr r7, [r12, #2216]
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
	ldr r7, [r12, #2220]
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
	ldr r7, [r12, #2224]
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
	ldr r7, [r12, #2228]
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
	ldr r7, [r12, #2232]
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
	ldr r7, [r12, #2236]
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
	sub r5, r3, #1
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	mov r10, lr
	mov r0, r12
	movw r1, #2240
	movw r2, #2176
	movw r3, #2560
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2688
	movw r2, #2240
	movw r3, #2240
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2752
	movw r2, #2688
	movw r3, #2240
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2688
	movw r2, #448
	movw r3, #2240
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2496
	movw r2, #2752
	movw r3, #2688
	bl {vg_brainpoolp512r1_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2752
	movw r2, #2496
	movw r3, #2624
	bl {vg_brainpoolp512r1_add_mod_p_umaal}
	mov lr, r10
	movw r4, #37437
	movt r4, #38414
	str r4, [r12, #832]
	movw r4, #38933
	movt r4, #18986
	str r4, [r12, #836]
	movw r4, #45473
	movt r4, #52064
	str r4, [r12, #840]
	movw r4, #32715
	movt r4, #35360
	str r4, [r12, #844]
	movw r4, #57401
	movt r4, #47528
	str r4, [r12, #848]
	movw r4, #26698
	movt r4, #43955
	str r4, [r12, #852]
	movw r4, #39440
	movt r4, #9969
	str r4, [r12, #856]
	movw r4, #26304
	movt r4, #24403
	str r4, [r12, #860]
	movw r4, #49692
	movt r4, #39948
	str r4, [r12, #864]
	movw r4, #59186
	movt r4, #46488
	str r4, [r12, #868]
	movw r4, #29827
	movt r4, #60658
	str r4, [r12, #872]
	movw r4, #9068
	movt r4, #62156
	str r4, [r12, #876]
	movw r4, #32513
	movt r4, #36082
	str r4, [r12, #880]
	movw r4, #14763
	movt r4, #53237
	str r4, [r12, #884]
	movw r4, #28962
	movt r4, #14074
	str r4, [r12, #888]
	movw r4, #26478
	movt r4, #10935
	str r4, [r12, #892]
	mov r11, #64
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #832]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #1024]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #1025]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #1026]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #1027]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #1028]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #1029]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #1030]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #1031]
	cmp r11, #0
	bne 21b
	ldr r4, [r12, #384]
	str r4, [r12, #1920]
	ldr r4, [r12, #388]
	str r4, [r12, #1924]
	ldr r4, [r12, #392]
	str r4, [r12, #1928]
	ldr r4, [r12, #396]
	str r4, [r12, #1932]
	ldr r4, [r12, #400]
	str r4, [r12, #1936]
	ldr r4, [r12, #404]
	str r4, [r12, #1940]
	ldr r4, [r12, #408]
	str r4, [r12, #1944]
	ldr r4, [r12, #412]
	str r4, [r12, #1948]
	ldr r4, [r12, #416]
	str r4, [r12, #1952]
	ldr r4, [r12, #420]
	str r4, [r12, #1956]
	ldr r4, [r12, #424]
	str r4, [r12, #1960]
	ldr r4, [r12, #428]
	str r4, [r12, #1964]
	ldr r4, [r12, #432]
	str r4, [r12, #1968]
	ldr r4, [r12, #436]
	str r4, [r12, #1972]
	ldr r4, [r12, #440]
	str r4, [r12, #1976]
	ldr r4, [r12, #444]
	str r4, [r12, #1980]
	mov r11, #512
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #1920
	movw r2, #1920
	movw r3, #1920
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1984
	movw r2, #1920
	movw r3, #2752
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #1024]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #1920]
	ldr r5, [r12, #1984]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1920]
	ldr r4, [r12, #1924]
	ldr r5, [r12, #1988]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1924]
	ldr r4, [r12, #1928]
	ldr r5, [r12, #1992]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1928]
	ldr r4, [r12, #1932]
	ldr r5, [r12, #1996]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1932]
	ldr r4, [r12, #1936]
	ldr r5, [r12, #2000]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1936]
	ldr r4, [r12, #1940]
	ldr r5, [r12, #2004]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1940]
	ldr r4, [r12, #1944]
	ldr r5, [r12, #2008]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1944]
	ldr r4, [r12, #1948]
	ldr r5, [r12, #2012]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1948]
	ldr r4, [r12, #1952]
	ldr r5, [r12, #2016]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1952]
	ldr r4, [r12, #1956]
	ldr r5, [r12, #2020]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1956]
	ldr r4, [r12, #1960]
	ldr r5, [r12, #2024]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1960]
	ldr r4, [r12, #1964]
	ldr r5, [r12, #2028]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1964]
	ldr r4, [r12, #1968]
	ldr r5, [r12, #2032]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1968]
	ldr r4, [r12, #1972]
	ldr r5, [r12, #2036]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1972]
	ldr r4, [r12, #1976]
	ldr r5, [r12, #2040]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1976]
	ldr r4, [r12, #1980]
	ldr r5, [r12, #2044]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1980]
	cmp r11, #0
	bne 22b
	mov r10, lr
	mov r0, r12
	movw r1, #2368
	movw r2, #1920
	movw r3, #320
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2432
	movw r2, #256
	movw r3, #2368
	bl {vg_brainpoolp512r1_sub_mod_p_umaal}
	mov lr, r10
	ldr r4, [r12, #2368]
	ldr r5, [r12, #2112]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	ldr r4, [r12, #2368]
	ldr r5, [r12, #2432]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2368]
	ldr r4, [r12, #2372]
	ldr r5, [r12, #2436]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2372]
	ldr r4, [r12, #2376]
	ldr r5, [r12, #2440]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2376]
	ldr r4, [r12, #2380]
	ldr r5, [r12, #2444]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2380]
	ldr r4, [r12, #2384]
	ldr r5, [r12, #2448]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2384]
	ldr r4, [r12, #2388]
	ldr r5, [r12, #2452]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2388]
	ldr r4, [r12, #2392]
	ldr r5, [r12, #2456]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2392]
	ldr r4, [r12, #2396]
	ldr r5, [r12, #2460]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2396]
	ldr r4, [r12, #2400]
	ldr r5, [r12, #2464]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2400]
	ldr r4, [r12, #2404]
	ldr r5, [r12, #2468]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2404]
	ldr r4, [r12, #2408]
	ldr r5, [r12, #2472]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2408]
	ldr r4, [r12, #2412]
	ldr r5, [r12, #2476]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2412]
	ldr r4, [r12, #2416]
	ldr r5, [r12, #2480]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2416]
	ldr r4, [r12, #2420]
	ldr r5, [r12, #2484]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2420]
	ldr r4, [r12, #2424]
	ldr r5, [r12, #2488]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2424]
	ldr r4, [r12, #2428]
	ldr r5, [r12, #2492]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2428]
	mov r10, lr
	mov r0, r12
	movw r1, #2304
	movw r2, #2368
	movw r3, #2560
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2688
	movw r2, #2304
	movw r3, #2304
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2496
	movw r2, #2688
	movw r3, #2752
	bl {vg_brainpoolp512r1_sub_mod_p_umaal}
	mov lr, r10
	ldr r5, [r12, #2496]
	ldr r4, [r12, #2500]
	orr r5, r5, r4
	ldr r4, [r12, #2504]
	orr r5, r5, r4
	ldr r4, [r12, #2508]
	orr r5, r5, r4
	ldr r4, [r12, #2512]
	orr r5, r5, r4
	ldr r4, [r12, #2516]
	orr r5, r5, r4
	ldr r4, [r12, #2520]
	orr r5, r5, r4
	ldr r4, [r12, #2524]
	orr r5, r5, r4
	ldr r4, [r12, #2528]
	orr r5, r5, r4
	ldr r4, [r12, #2532]
	orr r5, r5, r4
	ldr r4, [r12, #2536]
	orr r5, r5, r4
	ldr r4, [r12, #2540]
	orr r5, r5, r4
	ldr r4, [r12, #2544]
	orr r5, r5, r4
	ldr r4, [r12, #2548]
	orr r5, r5, r4
	ldr r4, [r12, #2552]
	orr r5, r5, r4
	ldr r4, [r12, #2556]
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
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	ldr r4, [r12, #2368]
	ldr r5, [r12, #2112]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	add r5, r10, #1
	mov r4, #0
	sub r5, r4, r5
	ldr r4, [r12, #2880]
	and r4, r4, r5
	str r4, [r12, #2880]
	ldr r10, [r12, #2880]
	mov r4, #4
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #2176]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #61]
	ldr r4, [r12, #2180]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #57]
	ldr r4, [r12, #2184]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #53]
	ldr r4, [r12, #2188]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #49]
	ldr r4, [r12, #2192]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #2196]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
	ldr r4, [r12, #2200]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #2204]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #2208]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #2212]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #2216]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #2220]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #2224]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #2228]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #2232]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #2236]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
	ldr r4, [r12, #2368]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #125]
	ldr r4, [r12, #2372]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #121]
	ldr r4, [r12, #2376]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #117]
	ldr r4, [r12, #2380]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #113]
	ldr r4, [r12, #2384]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #109]
	ldr r4, [r12, #2388]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #105]
	ldr r4, [r12, #2392]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #101]
	ldr r4, [r12, #2396]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #97]
	ldr r4, [r12, #2400]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #93]
	ldr r4, [r12, #2404]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #89]
	ldr r4, [r12, #2408]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #85]
	ldr r4, [r12, #2412]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #81]
	ldr r4, [r12, #2416]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #77]
	ldr r4, [r12, #2420]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #73]
	ldr r4, [r12, #2424]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #69]
	ldr r4, [r12, #2428]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #65]
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
