// The functions of `src/internal/vg_gf25519_r16_pow250_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_gf25519_r16_pow250_umaal:
	str r4, [r0, #1600]
	str r5, [r0, #1604]
	str r6, [r0, #1608]
	str r7, [r0, #1612]
	str r8, [r0, #1616]
	str r9, [r0, #1620]
	str r10, [r0, #1624]
	movw r1, #960
	movw r2, #192
	movw r3, #192
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
20:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 20b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r1, #1024
	movw r2, #960
	movw r3, #960
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
21:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 21b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r1, #1024
	movw r2, #1024
	movw r3, #1024
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
22:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 22b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r1, #1024
	movw r2, #192
	movw r3, #1024
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
23:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 23b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r1, #960
	movw r2, #960
	movw r3, #1024
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
24:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 24b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r1, #1088
	movw r2, #960
	movw r3, #960
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
25:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 25b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r1, #1024
	movw r2, #1024
	movw r3, #1088
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
26:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 26b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r1, #1088
	movw r2, #1024
	movw r3, #1024
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
27:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 27b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r10, #4
28:
	movw r1, #1088
	movw r2, #1088
	movw r3, #1088
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
29:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 29b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	subs r10, r10, #1
	bne 28b
	movw r1, #1024
	movw r2, #1088
	movw r3, #1024
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
210:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 210b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r1, #1088
	movw r2, #1024
	movw r3, #1024
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
211:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 211b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r10, #9
212:
	movw r1, #1088
	movw r2, #1088
	movw r3, #1088
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
213:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 213b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	subs r10, r10, #1
	bne 212b
	movw r1, #1088
	movw r2, #1088
	movw r3, #1024
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
214:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 214b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r1, #1152
	movw r2, #1088
	movw r3, #1088
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
215:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 215b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r10, #19
216:
	movw r1, #1152
	movw r2, #1152
	movw r3, #1152
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
217:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 217b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	subs r10, r10, #1
	bne 216b
	movw r1, #1088
	movw r2, #1152
	movw r3, #1088
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
218:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 218b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r1, #1088
	movw r2, #1088
	movw r3, #1088
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
219:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 219b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r10, #9
220:
	movw r1, #1088
	movw r2, #1088
	movw r3, #1088
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
221:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 221b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	subs r10, r10, #1
	bne 220b
	movw r1, #1024
	movw r2, #1088
	movw r3, #1024
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
222:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 222b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r1, #1088
	movw r2, #1024
	movw r3, #1024
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
223:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 223b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r10, #49
224:
	movw r1, #1088
	movw r2, #1088
	movw r3, #1088
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
225:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 225b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	subs r10, r10, #1
	bne 224b
	movw r1, #1088
	movw r2, #1088
	movw r3, #1024
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
226:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 226b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r1, #1152
	movw r2, #1088
	movw r3, #1088
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
227:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 227b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r10, #99
228:
	movw r1, #1152
	movw r2, #1152
	movw r3, #1152
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
229:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 229b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	subs r10, r10, #1
	bne 228b
	movw r1, #1088
	movw r2, #1152
	movw r3, #1088
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
230:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 230b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r1, #1088
	movw r2, #1088
	movw r3, #1088
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
231:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 231b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	movw r10, #49
232:
	movw r1, #1088
	movw r2, #1088
	movw r3, #1088
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
233:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 233b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	subs r10, r10, #1
	bne 232b
	movw r1, #1024
	movw r2, #1088
	movw r3, #1024
	add r8, r0, r1
	add r5, r0, r2
	add r9, r0, r3
	ldr r2, [r9, #0]
	ldr r3, [r9, #4]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1472]
	ldr r2, [r9, #8]
	ldr r3, [r9, #12]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1476]
	ldr r2, [r9, #16]
	ldr r3, [r9, #20]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1480]
	ldr r2, [r9, #24]
	ldr r3, [r9, #28]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1484]
	ldr r2, [r9, #32]
	ldr r3, [r9, #36]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1488]
	ldr r2, [r9, #40]
	ldr r3, [r9, #44]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1492]
	ldr r2, [r9, #48]
	ldr r3, [r9, #52]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1496]
	ldr r2, [r9, #56]
	ldr r3, [r9, #60]
	add r2, r2, r3, lsl #16
	str r2, [r0, #1500]
	mov r3, #0
	str r3, [r0, #1536]
	str r3, [r0, #1540]
	str r3, [r0, #1544]
	str r3, [r0, #1548]
	str r3, [r0, #1552]
	str r3, [r0, #1556]
	str r3, [r0, #1560]
	str r3, [r0, #1564]
	mov r7, r0
	mov r9, #8
234:
	ldr r1, [r5, #0]
	ldr r2, [r5, #4]
	add r1, r1, r2, lsl #16
	mov r4, #0
	ldr r2, [r0, #1472]
	ldr r3, [r7, #1536]
	umaal r3, r4, r1, r2
	str r3, [r7, #1536]
	ldr r2, [r0, #1476]
	ldr r3, [r7, #1540]
	umaal r3, r4, r1, r2
	str r3, [r7, #1540]
	ldr r2, [r0, #1480]
	ldr r3, [r7, #1544]
	umaal r3, r4, r1, r2
	str r3, [r7, #1544]
	ldr r2, [r0, #1484]
	ldr r3, [r7, #1548]
	umaal r3, r4, r1, r2
	str r3, [r7, #1548]
	ldr r2, [r0, #1488]
	ldr r3, [r7, #1552]
	umaal r3, r4, r1, r2
	str r3, [r7, #1552]
	ldr r2, [r0, #1492]
	ldr r3, [r7, #1556]
	umaal r3, r4, r1, r2
	str r3, [r7, #1556]
	ldr r2, [r0, #1496]
	ldr r3, [r7, #1560]
	umaal r3, r4, r1, r2
	str r3, [r7, #1560]
	ldr r2, [r0, #1500]
	ldr r3, [r7, #1564]
	umaal r3, r4, r1, r2
	str r3, [r7, #1564]
	str r4, [r7, #1568]
	add r7, r7, #4
	add r5, r5, #8
	subs r9, r9, #1
	bne 234b
	mov r9, r8
	mov r8, #38
	movw r6, #65535
	mov r4, #0
	ldr r3, [r0, #1536]
	ldr r2, [r0, #1568]
	umaal r3, r4, r8, r2
	str r3, [r0, #1536]
	ldr r3, [r0, #1540]
	ldr r2, [r0, #1572]
	umaal r3, r4, r8, r2
	str r3, [r0, #1540]
	ldr r3, [r0, #1544]
	ldr r2, [r0, #1576]
	umaal r3, r4, r8, r2
	str r3, [r0, #1544]
	ldr r3, [r0, #1548]
	ldr r2, [r0, #1580]
	umaal r3, r4, r8, r2
	str r3, [r0, #1548]
	ldr r3, [r0, #1552]
	ldr r2, [r0, #1584]
	umaal r3, r4, r8, r2
	str r3, [r0, #1552]
	ldr r3, [r0, #1556]
	ldr r2, [r0, #1588]
	umaal r3, r4, r8, r2
	str r3, [r0, #1556]
	ldr r3, [r0, #1560]
	ldr r2, [r0, #1592]
	umaal r3, r4, r8, r2
	str r3, [r0, #1560]
	ldr r3, [r0, #1564]
	ldr r2, [r0, #1596]
	umaal r3, r4, r8, r2
	str r3, [r0, #1564]
	mul r4, r4, r8
	mov r2, #0
	ldr r3, [r0, #1536]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #0]
	lsr r3, r3, #16
	str r3, [r9, #4]
	ldr r3, [r0, #1540]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #8]
	lsr r3, r3, #16
	str r3, [r9, #12]
	ldr r3, [r0, #1544]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #16]
	lsr r3, r3, #16
	str r3, [r9, #20]
	ldr r3, [r0, #1548]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #24]
	lsr r3, r3, #16
	str r3, [r9, #28]
	ldr r3, [r0, #1552]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #32]
	lsr r3, r3, #16
	str r3, [r9, #36]
	ldr r3, [r0, #1556]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #40]
	lsr r3, r3, #16
	str r3, [r9, #44]
	ldr r3, [r0, #1560]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #48]
	lsr r3, r3, #16
	str r3, [r9, #52]
	ldr r3, [r0, #1564]
	umaal r3, r4, r2, r2
	and r1, r3, r6
	str r1, [r9, #56]
	lsr r3, r3, #16
	str r3, [r9, #60]
	mul r4, r4, r8
	ldr r3, [r9, #0]
	add r3, r3, r4
	str r3, [r9, #0]
	ldr r4, [r0, #1600]
	ldr r5, [r0, #1604]
	ldr r6, [r0, #1608]
	ldr r7, [r0, #1612]
	ldr r8, [r0, #1616]
	ldr r9, [r0, #1620]
	ldr r10, [r0, #1624]
	bx lr
