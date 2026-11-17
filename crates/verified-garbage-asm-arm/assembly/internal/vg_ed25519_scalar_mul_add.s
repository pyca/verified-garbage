// The functions of `src/internal/vg_ed25519_scalar_mul_add.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_mul_add:
	ldr r12, [sp, #0]
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r8, [r12, #16]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str r0, [r12, #32]
	str r1, [r12, #36]
	str r2, [r12, #40]
	str r3, [r12, #44]
	mov r0, r12
	ldr r12, [r0, #36]
	ldrb r3, [r12, #0]
	ldrb r2, [r12, #1]
	add r3, r3, r2, lsl #8
	str r3, [r0, #64]
	ldrb r3, [r12, #2]
	ldrb r2, [r12, #3]
	add r3, r3, r2, lsl #8
	str r3, [r0, #68]
	ldrb r3, [r12, #4]
	ldrb r2, [r12, #5]
	add r3, r3, r2, lsl #8
	str r3, [r0, #72]
	ldrb r3, [r12, #6]
	ldrb r2, [r12, #7]
	add r3, r3, r2, lsl #8
	str r3, [r0, #76]
	ldrb r3, [r12, #8]
	ldrb r2, [r12, #9]
	add r3, r3, r2, lsl #8
	str r3, [r0, #80]
	ldrb r3, [r12, #10]
	ldrb r2, [r12, #11]
	add r3, r3, r2, lsl #8
	str r3, [r0, #84]
	ldrb r3, [r12, #12]
	ldrb r2, [r12, #13]
	add r3, r3, r2, lsl #8
	str r3, [r0, #88]
	ldrb r3, [r12, #14]
	ldrb r2, [r12, #15]
	add r3, r3, r2, lsl #8
	str r3, [r0, #92]
	ldrb r3, [r12, #16]
	ldrb r2, [r12, #17]
	add r3, r3, r2, lsl #8
	str r3, [r0, #96]
	ldrb r3, [r12, #18]
	ldrb r2, [r12, #19]
	add r3, r3, r2, lsl #8
	str r3, [r0, #100]
	ldrb r3, [r12, #20]
	ldrb r2, [r12, #21]
	add r3, r3, r2, lsl #8
	str r3, [r0, #104]
	ldrb r3, [r12, #22]
	ldrb r2, [r12, #23]
	add r3, r3, r2, lsl #8
	str r3, [r0, #108]
	ldrb r3, [r12, #24]
	ldrb r2, [r12, #25]
	add r3, r3, r2, lsl #8
	str r3, [r0, #112]
	ldrb r3, [r12, #26]
	ldrb r2, [r12, #27]
	add r3, r3, r2, lsl #8
	str r3, [r0, #116]
	ldrb r3, [r12, #28]
	ldrb r2, [r12, #29]
	add r3, r3, r2, lsl #8
	str r3, [r0, #120]
	ldrb r3, [r12, #30]
	ldrb r2, [r12, #31]
	add r3, r3, r2, lsl #8
	str r3, [r0, #124]
	ldr r12, [r0, #40]
	ldrb r3, [r12, #0]
	ldrb r2, [r12, #1]
	add r3, r3, r2, lsl #8
	str r3, [r0, #128]
	ldrb r3, [r12, #2]
	ldrb r2, [r12, #3]
	add r3, r3, r2, lsl #8
	str r3, [r0, #132]
	ldrb r3, [r12, #4]
	ldrb r2, [r12, #5]
	add r3, r3, r2, lsl #8
	str r3, [r0, #136]
	ldrb r3, [r12, #6]
	ldrb r2, [r12, #7]
	add r3, r3, r2, lsl #8
	str r3, [r0, #140]
	ldrb r3, [r12, #8]
	ldrb r2, [r12, #9]
	add r3, r3, r2, lsl #8
	str r3, [r0, #144]
	ldrb r3, [r12, #10]
	ldrb r2, [r12, #11]
	add r3, r3, r2, lsl #8
	str r3, [r0, #148]
	ldrb r3, [r12, #12]
	ldrb r2, [r12, #13]
	add r3, r3, r2, lsl #8
	str r3, [r0, #152]
	ldrb r3, [r12, #14]
	ldrb r2, [r12, #15]
	add r3, r3, r2, lsl #8
	str r3, [r0, #156]
	ldrb r3, [r12, #16]
	ldrb r2, [r12, #17]
	add r3, r3, r2, lsl #8
	str r3, [r0, #160]
	ldrb r3, [r12, #18]
	ldrb r2, [r12, #19]
	add r3, r3, r2, lsl #8
	str r3, [r0, #164]
	ldrb r3, [r12, #20]
	ldrb r2, [r12, #21]
	add r3, r3, r2, lsl #8
	str r3, [r0, #168]
	ldrb r3, [r12, #22]
	ldrb r2, [r12, #23]
	add r3, r3, r2, lsl #8
	str r3, [r0, #172]
	ldrb r3, [r12, #24]
	ldrb r2, [r12, #25]
	add r3, r3, r2, lsl #8
	str r3, [r0, #176]
	ldrb r3, [r12, #26]
	ldrb r2, [r12, #27]
	add r3, r3, r2, lsl #8
	str r3, [r0, #180]
	ldrb r3, [r12, #28]
	ldrb r2, [r12, #29]
	add r3, r3, r2, lsl #8
	str r3, [r0, #184]
	ldrb r3, [r12, #30]
	ldrb r2, [r12, #31]
	add r3, r3, r2, lsl #8
	str r3, [r0, #188]
	ldr r12, [r0, #44]
	ldrb r3, [r12, #0]
	ldrb r2, [r12, #1]
	add r3, r3, r2, lsl #8
	str r3, [r0, #192]
	ldrb r3, [r12, #2]
	ldrb r2, [r12, #3]
	add r3, r3, r2, lsl #8
	str r3, [r0, #196]
	ldrb r3, [r12, #4]
	ldrb r2, [r12, #5]
	add r3, r3, r2, lsl #8
	str r3, [r0, #200]
	ldrb r3, [r12, #6]
	ldrb r2, [r12, #7]
	add r3, r3, r2, lsl #8
	str r3, [r0, #204]
	ldrb r3, [r12, #8]
	ldrb r2, [r12, #9]
	add r3, r3, r2, lsl #8
	str r3, [r0, #208]
	ldrb r3, [r12, #10]
	ldrb r2, [r12, #11]
	add r3, r3, r2, lsl #8
	str r3, [r0, #212]
	ldrb r3, [r12, #12]
	ldrb r2, [r12, #13]
	add r3, r3, r2, lsl #8
	str r3, [r0, #216]
	ldrb r3, [r12, #14]
	ldrb r2, [r12, #15]
	add r3, r3, r2, lsl #8
	str r3, [r0, #220]
	ldrb r3, [r12, #16]
	ldrb r2, [r12, #17]
	add r3, r3, r2, lsl #8
	str r3, [r0, #224]
	ldrb r3, [r12, #18]
	ldrb r2, [r12, #19]
	add r3, r3, r2, lsl #8
	str r3, [r0, #228]
	ldrb r3, [r12, #20]
	ldrb r2, [r12, #21]
	add r3, r3, r2, lsl #8
	str r3, [r0, #232]
	ldrb r3, [r12, #22]
	ldrb r2, [r12, #23]
	add r3, r3, r2, lsl #8
	str r3, [r0, #236]
	ldrb r3, [r12, #24]
	ldrb r2, [r12, #25]
	add r3, r3, r2, lsl #8
	str r3, [r0, #240]
	ldrb r3, [r12, #26]
	ldrb r2, [r12, #27]
	add r3, r3, r2, lsl #8
	str r3, [r0, #244]
	ldrb r3, [r12, #28]
	ldrb r2, [r12, #29]
	add r3, r3, r2, lsl #8
	str r3, [r0, #248]
	ldrb r3, [r12, #30]
	ldrb r2, [r12, #31]
	add r3, r3, r2, lsl #8
	str r3, [r0, #252]
	ldr r10, [r0, #32]
	movw r6, #65535
	mov r8, #38
	mov r5, #0
	mov r3, #0
	str r3, [r0, #1472]
	str r3, [r0, #1476]
	str r3, [r0, #1480]
	str r3, [r0, #1484]
	str r3, [r0, #1488]
	str r3, [r0, #1492]
	str r3, [r0, #1496]
	str r3, [r0, #1500]
	str r3, [r0, #1504]
	str r3, [r0, #1508]
	str r3, [r0, #1512]
	str r3, [r0, #1516]
	str r3, [r0, #1520]
	str r3, [r0, #1524]
	str r3, [r0, #1528]
	str r3, [r0, #1532]
	mov r7, r0
	mov r9, #16
20:
	ldr r1, [r7, #128]
	mov r5, #0
	ldr r2, [r0, #192]
	mul r2, r1, r2
	ldr r3, [r7, #1472]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1472]
	lsr r5, r3, #16
	ldr r2, [r0, #196]
	mul r2, r1, r2
	ldr r3, [r7, #1476]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1476]
	lsr r5, r3, #16
	ldr r2, [r0, #200]
	mul r2, r1, r2
	ldr r3, [r7, #1480]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1480]
	lsr r5, r3, #16
	ldr r2, [r0, #204]
	mul r2, r1, r2
	ldr r3, [r7, #1484]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1484]
	lsr r5, r3, #16
	ldr r2, [r0, #208]
	mul r2, r1, r2
	ldr r3, [r7, #1488]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1488]
	lsr r5, r3, #16
	ldr r2, [r0, #212]
	mul r2, r1, r2
	ldr r3, [r7, #1492]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1492]
	lsr r5, r3, #16
	ldr r2, [r0, #216]
	mul r2, r1, r2
	ldr r3, [r7, #1496]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1496]
	lsr r5, r3, #16
	ldr r2, [r0, #220]
	mul r2, r1, r2
	ldr r3, [r7, #1500]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1500]
	lsr r5, r3, #16
	ldr r2, [r0, #224]
	mul r2, r1, r2
	ldr r3, [r7, #1504]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1504]
	lsr r5, r3, #16
	ldr r2, [r0, #228]
	mul r2, r1, r2
	ldr r3, [r7, #1508]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1508]
	lsr r5, r3, #16
	ldr r2, [r0, #232]
	mul r2, r1, r2
	ldr r3, [r7, #1512]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1512]
	lsr r5, r3, #16
	ldr r2, [r0, #236]
	mul r2, r1, r2
	ldr r3, [r7, #1516]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1516]
	lsr r5, r3, #16
	ldr r2, [r0, #240]
	mul r2, r1, r2
	ldr r3, [r7, #1520]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1520]
	lsr r5, r3, #16
	ldr r2, [r0, #244]
	mul r2, r1, r2
	ldr r3, [r7, #1524]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1524]
	lsr r5, r3, #16
	ldr r2, [r0, #248]
	mul r2, r1, r2
	ldr r3, [r7, #1528]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1528]
	lsr r5, r3, #16
	ldr r2, [r0, #252]
	mul r2, r1, r2
	ldr r3, [r7, #1532]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #1532]
	lsr r5, r3, #16
	str r5, [r7, #1536]
	add r7, r7, #4
	subs r9, r9, #1
	bne 20b
	movw r6, #65535
	mov r5, #0
	ldr r3, [r0, #1472]
	ldr r2, [r0, #64]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1472]
	lsr r5, r3, #16
	ldr r3, [r0, #1476]
	ldr r2, [r0, #68]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1476]
	lsr r5, r3, #16
	ldr r3, [r0, #1480]
	ldr r2, [r0, #72]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1480]
	lsr r5, r3, #16
	ldr r3, [r0, #1484]
	ldr r2, [r0, #76]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1484]
	lsr r5, r3, #16
	ldr r3, [r0, #1488]
	ldr r2, [r0, #80]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1488]
	lsr r5, r3, #16
	ldr r3, [r0, #1492]
	ldr r2, [r0, #84]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1492]
	lsr r5, r3, #16
	ldr r3, [r0, #1496]
	ldr r2, [r0, #88]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1496]
	lsr r5, r3, #16
	ldr r3, [r0, #1500]
	ldr r2, [r0, #92]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1500]
	lsr r5, r3, #16
	ldr r3, [r0, #1504]
	ldr r2, [r0, #96]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1504]
	lsr r5, r3, #16
	ldr r3, [r0, #1508]
	ldr r2, [r0, #100]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1508]
	lsr r5, r3, #16
	ldr r3, [r0, #1512]
	ldr r2, [r0, #104]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1512]
	lsr r5, r3, #16
	ldr r3, [r0, #1516]
	ldr r2, [r0, #108]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1516]
	lsr r5, r3, #16
	ldr r3, [r0, #1520]
	ldr r2, [r0, #112]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1520]
	lsr r5, r3, #16
	ldr r3, [r0, #1524]
	ldr r2, [r0, #116]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1524]
	lsr r5, r3, #16
	ldr r3, [r0, #1528]
	ldr r2, [r0, #120]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1528]
	lsr r5, r3, #16
	ldr r3, [r0, #1532]
	ldr r2, [r0, #124]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1532]
	lsr r5, r3, #16
	ldr r3, [r0, #1536]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1536]
	lsr r5, r3, #16
	ldr r3, [r0, #1540]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1540]
	lsr r5, r3, #16
	ldr r3, [r0, #1544]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1544]
	lsr r5, r3, #16
	ldr r3, [r0, #1548]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1548]
	lsr r5, r3, #16
	ldr r3, [r0, #1552]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1552]
	lsr r5, r3, #16
	ldr r3, [r0, #1556]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1556]
	lsr r5, r3, #16
	ldr r3, [r0, #1560]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1560]
	lsr r5, r3, #16
	ldr r3, [r0, #1564]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1564]
	lsr r5, r3, #16
	ldr r3, [r0, #1568]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1568]
	lsr r5, r3, #16
	ldr r3, [r0, #1572]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1572]
	lsr r5, r3, #16
	ldr r3, [r0, #1576]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1576]
	lsr r5, r3, #16
	ldr r3, [r0, #1580]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1580]
	lsr r5, r3, #16
	ldr r3, [r0, #1584]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1584]
	lsr r5, r3, #16
	ldr r3, [r0, #1588]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1588]
	lsr r5, r3, #16
	ldr r3, [r0, #1592]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1592]
	lsr r5, r3, #16
	ldr r3, [r0, #1596]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1596]
	lsr r5, r3, #16
	mov r8, r10
	movw r6, #65535
	mov r3, #0
	str r3, [r0, #384]
	str r3, [r0, #388]
	str r3, [r0, #392]
	str r3, [r0, #396]
	str r3, [r0, #400]
	str r3, [r0, #404]
	str r3, [r0, #408]
	str r3, [r0, #412]
	str r3, [r0, #416]
	mov r7, r0
	mov r9, #16
21:
	ldr r1, [r7, #1536]
	mov r5, #0
	ldr r3, [r7, #384]
	movw r2, #16080
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #384]
	lsr r5, r3, #16
	ldr r3, [r7, #388]
	movw r2, #53085
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #388]
	lsr r5, r3, #16
	ldr r3, [r7, #392]
	movw r2, #12709
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #392]
	lsr r5, r3, #16
	ldr r3, [r7, #396]
	movw r2, #33062
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #396]
	lsr r5, r3, #16
	ldr r3, [r7, #400]
	movw r2, #52581
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #400]
	lsr r5, r3, #16
	ldr r3, [r7, #404]
	movw r2, #12153
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #404]
	lsr r5, r3, #16
	ldr r3, [r7, #408]
	movw r2, #40426
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #408]
	lsr r5, r3, #16
	ldr r3, [r7, #412]
	movw r2, #19951
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #412]
	lsr r5, r3, #16
	ldr r3, [r7, #416]
	movw r2, #1
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #416]
	lsr r5, r3, #16
	str r5, [r7, #420]
	add r7, r7, #4
	subs r9, r9, #1
	bne 21b
	mov r3, #0
	str r3, [r0, #512]
	str r3, [r0, #516]
	str r3, [r0, #520]
	str r3, [r0, #524]
	str r3, [r0, #528]
	str r3, [r0, #532]
	str r3, [r0, #536]
	str r3, [r0, #540]
	str r3, [r0, #544]
	mov r7, r0
	mov r9, #9
22:
	ldr r1, [r7, #448]
	mov r5, #0
	ldr r3, [r7, #512]
	movw r2, #16080
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #512]
	lsr r5, r3, #16
	ldr r3, [r7, #516]
	movw r2, #53085
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #516]
	lsr r5, r3, #16
	ldr r3, [r7, #520]
	movw r2, #12709
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #520]
	lsr r5, r3, #16
	ldr r3, [r7, #524]
	movw r2, #33062
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #524]
	lsr r5, r3, #16
	ldr r3, [r7, #528]
	movw r2, #52581
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #528]
	lsr r5, r3, #16
	ldr r3, [r7, #532]
	movw r2, #12153
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #532]
	lsr r5, r3, #16
	ldr r3, [r7, #536]
	movw r2, #40426
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #536]
	lsr r5, r3, #16
	ldr r3, [r7, #540]
	movw r2, #19951
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #540]
	lsr r5, r3, #16
	ldr r3, [r7, #544]
	movw r2, #1
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r7, #544]
	lsr r5, r3, #16
	str r5, [r7, #548]
	add r7, r7, #4
	subs r9, r9, #1
	bne 22b
	ldr r2, [r0, #576]
	mov r1, #1
	sub r1, r1, r2
	mov r5, #1
	ldr r3, [r0, #1472]
	add r3, r3, r6
	ldr r2, [r0, #384]
	sub r3, r3, r2
	ldr r2, [r0, #512]
	add r3, r3, r2
	movw r2, #16080
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #256]
	lsr r5, r3, #16
	ldr r3, [r0, #1476]
	add r3, r3, r6
	ldr r2, [r0, #388]
	sub r3, r3, r2
	ldr r2, [r0, #516]
	add r3, r3, r2
	movw r2, #53085
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #260]
	lsr r5, r3, #16
	ldr r3, [r0, #1480]
	add r3, r3, r6
	ldr r2, [r0, #392]
	sub r3, r3, r2
	ldr r2, [r0, #520]
	add r3, r3, r2
	movw r2, #12709
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #264]
	lsr r5, r3, #16
	ldr r3, [r0, #1484]
	add r3, r3, r6
	ldr r2, [r0, #396]
	sub r3, r3, r2
	ldr r2, [r0, #524]
	add r3, r3, r2
	movw r2, #33062
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #268]
	lsr r5, r3, #16
	ldr r3, [r0, #1488]
	add r3, r3, r6
	ldr r2, [r0, #400]
	sub r3, r3, r2
	ldr r2, [r0, #528]
	add r3, r3, r2
	movw r2, #52581
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #272]
	lsr r5, r3, #16
	ldr r3, [r0, #1492]
	add r3, r3, r6
	ldr r2, [r0, #404]
	sub r3, r3, r2
	ldr r2, [r0, #532]
	add r3, r3, r2
	movw r2, #12153
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #276]
	lsr r5, r3, #16
	ldr r3, [r0, #1496]
	add r3, r3, r6
	ldr r2, [r0, #408]
	sub r3, r3, r2
	ldr r2, [r0, #536]
	add r3, r3, r2
	movw r2, #40426
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #280]
	lsr r5, r3, #16
	ldr r3, [r0, #1500]
	add r3, r3, r6
	ldr r2, [r0, #412]
	sub r3, r3, r2
	ldr r2, [r0, #540]
	add r3, r3, r2
	movw r2, #19951
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #284]
	lsr r5, r3, #16
	ldr r3, [r0, #1504]
	add r3, r3, r6
	ldr r2, [r0, #416]
	sub r3, r3, r2
	ldr r2, [r0, #544]
	add r3, r3, r2
	movw r2, #1
	mla r3, r1, r2, r3
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #288]
	lsr r5, r3, #16
	ldr r3, [r0, #1508]
	add r3, r3, r6
	ldr r2, [r0, #420]
	sub r3, r3, r2
	ldr r2, [r0, #548]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #292]
	lsr r5, r3, #16
	ldr r3, [r0, #1512]
	add r3, r3, r6
	ldr r2, [r0, #424]
	sub r3, r3, r2
	ldr r2, [r0, #552]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #296]
	lsr r5, r3, #16
	ldr r3, [r0, #1516]
	add r3, r3, r6
	ldr r2, [r0, #428]
	sub r3, r3, r2
	ldr r2, [r0, #556]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #300]
	lsr r5, r3, #16
	ldr r3, [r0, #1520]
	add r3, r3, r6
	ldr r2, [r0, #432]
	sub r3, r3, r2
	ldr r2, [r0, #560]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #304]
	lsr r5, r3, #16
	ldr r3, [r0, #1524]
	add r3, r3, r6
	ldr r2, [r0, #436]
	sub r3, r3, r2
	ldr r2, [r0, #564]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #308]
	lsr r5, r3, #16
	ldr r3, [r0, #1528]
	add r3, r3, r6
	ldr r2, [r0, #440]
	sub r3, r3, r2
	ldr r2, [r0, #568]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #312]
	lsr r5, r3, #16
	ldr r3, [r0, #1532]
	add r3, r3, r6
	ldr r2, [r0, #444]
	sub r3, r3, r2
	ldr r2, [r0, #572]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #316]
	lsr r5, r3, #16
	ldr r3, [r0, #316]
	lsr r2, r3, #12
	add r2, r2, r5, lsl #4
	mov r1, #64
	sub r1, r1, r2
	lsl r3, r3, #20
	lsr r3, r3, #20
	str r3, [r0, #316]
	mov r5, #0
	ldr r3, [r0, #256]
	movw r2, #54253
	mla r3, r1, r2, r3
	movw r2, #55469
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #256]
	lsr r5, r3, #16
	ldr r3, [r0, #260]
	movw r2, #23797
	mla r3, r1, r2, r3
	movw r2, #8064
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #260]
	lsr r5, r3, #16
	ldr r3, [r0, #264]
	movw r2, #25370
	mla r3, r1, r2, r3
	movw r2, #40067
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #264]
	lsr r5, r3, #16
	ldr r3, [r0, #268]
	movw r2, #22546
	mla r3, r1, r2, r3
	movw r2, #21369
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #268]
	lsr r5, r3, #16
	ldr r3, [r0, #272]
	movw r2, #40150
	mla r3, r1, r2, r3
	movw r2, #26432
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #272]
	lsr r5, r3, #16
	ldr r3, [r0, #276]
	movw r2, #41719
	mla r3, r1, r2, r3
	movw r2, #58640
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #276]
	lsr r5, r3, #16
	ldr r3, [r0, #280]
	movw r2, #63966
	mla r3, r1, r2, r3
	movw r2, #33333
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #280]
	lsr r5, r3, #16
	ldr r3, [r0, #284]
	movw r2, #5342
	mla r3, r1, r2, r3
	movw r2, #56608
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #284]
	lsr r5, r3, #16
	ldr r3, [r0, #288]
	movw r2, #65530
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #288]
	lsr r5, r3, #16
	ldr r3, [r0, #292]
	movw r2, #65535
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #292]
	lsr r5, r3, #16
	ldr r3, [r0, #296]
	movw r2, #65535
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #296]
	lsr r5, r3, #16
	ldr r3, [r0, #300]
	movw r2, #65535
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #300]
	lsr r5, r3, #16
	ldr r3, [r0, #304]
	movw r2, #65535
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #304]
	lsr r5, r3, #16
	ldr r3, [r0, #308]
	movw r2, #65535
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #308]
	lsr r5, r3, #16
	ldr r3, [r0, #312]
	movw r2, #65535
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #312]
	lsr r5, r3, #16
	ldr r3, [r0, #316]
	movw r2, #4095
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #316]
	lsr r5, r3, #16
	mov r5, #1
	ldr r3, [r0, #256]
	movw r2, #11282
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #320]
	lsr r5, r3, #16
	ldr r3, [r0, #260]
	movw r2, #41738
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #324]
	lsr r5, r3, #16
	ldr r3, [r0, #264]
	movw r2, #40165
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #328]
	lsr r5, r3, #16
	ldr r3, [r0, #268]
	movw r2, #42989
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #332]
	lsr r5, r3, #16
	ldr r3, [r0, #272]
	movw r2, #25385
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #336]
	lsr r5, r3, #16
	ldr r3, [r0, #276]
	movw r2, #23816
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #340]
	lsr r5, r3, #16
	ldr r3, [r0, #280]
	movw r2, #1569
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #344]
	lsr r5, r3, #16
	ldr r3, [r0, #284]
	movw r2, #60193
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #348]
	lsr r5, r3, #16
	ldr r3, [r0, #288]
	movw r2, #65535
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #352]
	lsr r5, r3, #16
	ldr r3, [r0, #292]
	movw r2, #65535
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #356]
	lsr r5, r3, #16
	ldr r3, [r0, #296]
	movw r2, #65535
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #360]
	lsr r5, r3, #16
	ldr r3, [r0, #300]
	movw r2, #65535
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #364]
	lsr r5, r3, #16
	ldr r3, [r0, #304]
	movw r2, #65535
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #368]
	lsr r5, r3, #16
	ldr r3, [r0, #308]
	movw r2, #65535
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #372]
	lsr r5, r3, #16
	ldr r3, [r0, #312]
	movw r2, #65535
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #376]
	lsr r5, r3, #16
	ldr r3, [r0, #316]
	movw r2, #61439
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #380]
	lsr r5, r3, #16
	mov r9, #0
	sub r9, r9, r5
	ldr r2, [r0, #256]
	ldr r3, [r0, #320]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #256]
	str r3, [r0, #320]
	ldr r2, [r0, #260]
	ldr r3, [r0, #324]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #260]
	str r3, [r0, #324]
	ldr r2, [r0, #264]
	ldr r3, [r0, #328]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #264]
	str r3, [r0, #328]
	ldr r2, [r0, #268]
	ldr r3, [r0, #332]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #268]
	str r3, [r0, #332]
	ldr r2, [r0, #272]
	ldr r3, [r0, #336]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #272]
	str r3, [r0, #336]
	ldr r2, [r0, #276]
	ldr r3, [r0, #340]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #276]
	str r3, [r0, #340]
	ldr r2, [r0, #280]
	ldr r3, [r0, #344]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #280]
	str r3, [r0, #344]
	ldr r2, [r0, #284]
	ldr r3, [r0, #348]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #284]
	str r3, [r0, #348]
	ldr r2, [r0, #288]
	ldr r3, [r0, #352]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #288]
	str r3, [r0, #352]
	ldr r2, [r0, #292]
	ldr r3, [r0, #356]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #292]
	str r3, [r0, #356]
	ldr r2, [r0, #296]
	ldr r3, [r0, #360]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #296]
	str r3, [r0, #360]
	ldr r2, [r0, #300]
	ldr r3, [r0, #364]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #300]
	str r3, [r0, #364]
	ldr r2, [r0, #304]
	ldr r3, [r0, #368]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #304]
	str r3, [r0, #368]
	ldr r2, [r0, #308]
	ldr r3, [r0, #372]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #308]
	str r3, [r0, #372]
	ldr r2, [r0, #312]
	ldr r3, [r0, #376]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #312]
	str r3, [r0, #376]
	ldr r2, [r0, #316]
	ldr r3, [r0, #380]
	eor r4, r2, r3
	and r4, r4, r9
	eor r2, r2, r4
	eor r3, r3, r4
	str r2, [r0, #316]
	str r3, [r0, #380]
	mov r12, r8
	ldr r3, [r0, #256]
	strb r3, [r12, #0]
	lsr r3, r3, #8
	strb r3, [r12, #1]
	ldr r3, [r0, #260]
	strb r3, [r12, #2]
	lsr r3, r3, #8
	strb r3, [r12, #3]
	ldr r3, [r0, #264]
	strb r3, [r12, #4]
	lsr r3, r3, #8
	strb r3, [r12, #5]
	ldr r3, [r0, #268]
	strb r3, [r12, #6]
	lsr r3, r3, #8
	strb r3, [r12, #7]
	ldr r3, [r0, #272]
	strb r3, [r12, #8]
	lsr r3, r3, #8
	strb r3, [r12, #9]
	ldr r3, [r0, #276]
	strb r3, [r12, #10]
	lsr r3, r3, #8
	strb r3, [r12, #11]
	ldr r3, [r0, #280]
	strb r3, [r12, #12]
	lsr r3, r3, #8
	strb r3, [r12, #13]
	ldr r3, [r0, #284]
	strb r3, [r12, #14]
	lsr r3, r3, #8
	strb r3, [r12, #15]
	ldr r3, [r0, #288]
	strb r3, [r12, #16]
	lsr r3, r3, #8
	strb r3, [r12, #17]
	ldr r3, [r0, #292]
	strb r3, [r12, #18]
	lsr r3, r3, #8
	strb r3, [r12, #19]
	ldr r3, [r0, #296]
	strb r3, [r12, #20]
	lsr r3, r3, #8
	strb r3, [r12, #21]
	ldr r3, [r0, #300]
	strb r3, [r12, #22]
	lsr r3, r3, #8
	strb r3, [r12, #23]
	ldr r3, [r0, #304]
	strb r3, [r12, #24]
	lsr r3, r3, #8
	strb r3, [r12, #25]
	ldr r3, [r0, #308]
	strb r3, [r12, #26]
	lsr r3, r3, #8
	strb r3, [r12, #27]
	ldr r3, [r0, #312]
	strb r3, [r12, #28]
	lsr r3, r3, #8
	strb r3, [r12, #29]
	ldr r3, [r0, #316]
	strb r3, [r12, #30]
	lsr r3, r3, #8
	strb r3, [r12, #31]
	ldr r4, [r0, #0]
	ldr r5, [r0, #4]
	ldr r6, [r0, #8]
	ldr r7, [r0, #12]
	ldr r8, [r0, #16]
	ldr r9, [r0, #20]
	ldr r10, [r0, #24]
	ldr r11, [r0, #28]
	bx lr
