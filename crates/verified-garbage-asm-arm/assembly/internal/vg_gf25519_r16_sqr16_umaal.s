// The functions of `src/internal/vg_gf25519_r16_sqr16_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_gf25519_r16_sqr16_umaal:
	str r4, [r0, #1600]
	str r5, [r0, #1604]
	str r6, [r0, #1608]
	str r7, [r0, #1612]
	str r8, [r0, #1616]
	str r9, [r0, #1620]
	str r10, [r0, #1624]
20:
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
	subs r10, r10, #1
	bne 20b
	ldr r4, [r0, #1600]
	ldr r5, [r0, #1604]
	ldr r6, [r0, #1608]
	ldr r7, [r0, #1612]
	ldr r8, [r0, #1616]
	ldr r9, [r0, #1620]
	ldr r10, [r0, #1624]
	bx lr
