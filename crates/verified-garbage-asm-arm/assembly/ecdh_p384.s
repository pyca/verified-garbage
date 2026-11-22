// The functions of `src/ecdh_p384.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdh_p384:
	mov r12, r3
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
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #1552]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #1556]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1560]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1564]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1568]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1572]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1576]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1580]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1584]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1588]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1592]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1596]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #1600]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #1604]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1608]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1612]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1616]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1620]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1624]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1628]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1632]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1636]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1640]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1644]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #1648]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #1652]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1656]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1660]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1664]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1668]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1672]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1676]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1680]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1684]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1688]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1692]
	movw r10, #:lower16:({VG_P384_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P384_FRAME_CONSTS}
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
	add r10, r10, #48
	add r9, r9, #48
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #2176]
	mov r11, #48
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #1552]
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
	mov r11, #48
22:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #640]
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
	bne 22b
	mov r11, #48
23:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #688]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #768]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #769]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #770]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #771]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #772]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #773]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #774]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #775]
	cmp r11, #0
	bne 23b
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1936]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #1940]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1944]
	movw r4, #2
	movt r4, #0
	str r4, [r12, #1948]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1952]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #1956]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1960]
	movw r4, #2
	movt r4, #0
	str r4, [r12, #1964]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1968]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1972]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1976]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1980]
	movw r4, #11724
	movt r4, #40257
	str r4, [r12, #1984]
	movw r4, #34929
	movt r4, #2065
	str r4, [r12, #1988]
	movw r4, #13036
	movt r4, #31308
	str r4, [r12, #1992]
	movw r4, #44504
	movt r4, #63273
	str r4, [r12, #1996]
	movw r4, #558
	movt r4, #6432
	str r4, [r12, #2000]
	movw r4, #8347
	movt r4, #30706
	str r4, [r12, #2004]
	movw r4, #35554
	movt r4, #38035
	str r4, [r12, #2008]
	movw r4, #19438
	movt r4, #58167
	str r4, [r12, #2012]
	movw r4, #8340
	movt r4, #7938
	str r4, [r12, #2016]
	movw r4, #8692
	movt r4, #46635
	str r4, [r12, #2020]
	movw r4, #49145
	movt r4, #24655
	str r4, [r12, #2024]
	movw r4, #4427
	movt r4, #52488
	str r4, [r12, #2028]
	add r6, r2, #1
	ldr r4, [r6, #44]
	rev r4, r4
	str r4, [r12, #1648]
	ldr r4, [r6, #40]
	rev r4, r4
	str r4, [r12, #1652]
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #1656]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #1660]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1664]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1668]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1672]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1676]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1680]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1684]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1688]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1692]
	add r6, r6, #48
	ldr r4, [r6, #44]
	rev r4, r4
	str r4, [r12, #1792]
	ldr r4, [r6, #40]
	rev r4, r4
	str r4, [r12, #1796]
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #1800]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #1804]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1808]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1812]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1816]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1820]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1824]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1828]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1832]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1836]
	ldrb r4, [r2, #0]
	eor r4, r4, #4
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1648]
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
	ldr r7, [r12, #1652]
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
	ldr r7, [r12, #1656]
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
	ldr r7, [r12, #1660]
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
	ldr r7, [r12, #1664]
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
	ldr r7, [r12, #1668]
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
	ldr r7, [r12, #1672]
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
	ldr r7, [r12, #1676]
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
	ldr r7, [r12, #1680]
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
	ldr r7, [r12, #1684]
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
	ldr r7, [r12, #1688]
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
	ldr r7, [r12, #1692]
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
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1792]
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
	ldr r7, [r12, #1796]
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
	ldr r7, [r12, #1800]
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
	ldr r7, [r12, #1804]
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
	ldr r7, [r12, #1808]
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
	ldr r7, [r12, #1812]
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
	ldr r7, [r12, #1816]
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
	ldr r7, [r12, #1820]
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
	ldr r7, [r12, #1824]
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
	ldr r7, [r12, #1828]
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
	ldr r7, [r12, #1832]
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
	ldr r7, [r12, #1836]
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
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	mov r10, lr
	mov r0, r12
	movw r1, #1696
	movw r2, #1648
	movw r3, #1936
	bl {vg_p384_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1792
	movw r3, #1936
	bl {vg_p384_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1840
	movw r2, #1744
	movw r3, #1744
	bl {vg_p384_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #1696
	movw r3, #1696
	bl {vg_p384_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2080
	movw r2, #2032
	movw r3, #1696
	bl {vg_p384_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #352
	movw r3, #1696
	bl {vg_p384_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1888
	movw r2, #2080
	movw r3, #2032
	bl {vg_p384_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2080
	movw r2, #1888
	movw r3, #1984
	bl {vg_p384_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #1840
	movw r3, #2080
	bl {vg_p384_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #2032]
	ldr r4, [r12, #2036]
	orr r5, r5, r4
	ldr r4, [r12, #2040]
	orr r5, r5, r4
	ldr r4, [r12, #2044]
	orr r5, r5, r4
	ldr r4, [r12, #2048]
	orr r5, r5, r4
	ldr r4, [r12, #2052]
	orr r5, r5, r4
	ldr r4, [r12, #2056]
	orr r5, r5, r4
	ldr r4, [r12, #2060]
	orr r5, r5, r4
	ldr r4, [r12, #2064]
	orr r5, r5, r4
	ldr r4, [r12, #2068]
	orr r5, r5, r4
	ldr r4, [r12, #2072]
	orr r5, r5, r4
	ldr r4, [r12, #2076]
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
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	ldr r10, [r12, #2176]
	ldr r4, [r12, #448]
	ldr r5, [r12, #1696]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1888]
	ldr r4, [r12, #452]
	ldr r5, [r12, #1700]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1892]
	ldr r4, [r12, #456]
	ldr r5, [r12, #1704]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1896]
	ldr r4, [r12, #460]
	ldr r5, [r12, #1708]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1900]
	ldr r4, [r12, #464]
	ldr r5, [r12, #1712]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1904]
	ldr r4, [r12, #468]
	ldr r5, [r12, #1716]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1908]
	ldr r4, [r12, #472]
	ldr r5, [r12, #1720]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1912]
	ldr r4, [r12, #476]
	ldr r5, [r12, #1724]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1916]
	ldr r4, [r12, #480]
	ldr r5, [r12, #1728]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1920]
	ldr r4, [r12, #484]
	ldr r5, [r12, #1732]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1924]
	ldr r4, [r12, #488]
	ldr r5, [r12, #1736]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1928]
	ldr r4, [r12, #492]
	ldr r5, [r12, #1740]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1932]
	ldr r4, [r12, #496]
	ldr r5, [r12, #1744]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2128]
	ldr r4, [r12, #500]
	ldr r5, [r12, #1748]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2132]
	ldr r4, [r12, #504]
	ldr r5, [r12, #1752]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2136]
	ldr r4, [r12, #508]
	ldr r5, [r12, #1756]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2140]
	ldr r4, [r12, #512]
	ldr r5, [r12, #1760]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2144]
	ldr r4, [r12, #516]
	ldr r5, [r12, #1764]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2148]
	ldr r4, [r12, #520]
	ldr r5, [r12, #1768]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2152]
	ldr r4, [r12, #524]
	ldr r5, [r12, #1772]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2156]
	ldr r4, [r12, #528]
	ldr r5, [r12, #1776]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2160]
	ldr r4, [r12, #532]
	ldr r5, [r12, #1780]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2164]
	ldr r4, [r12, #536]
	ldr r5, [r12, #1784]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2168]
	ldr r4, [r12, #540]
	ldr r5, [r12, #1788]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2172]
	ldr r4, [r12, #1888]
	str r4, [r12, #736]
	ldr r4, [r12, #1892]
	str r4, [r12, #740]
	ldr r4, [r12, #1896]
	str r4, [r12, #744]
	ldr r4, [r12, #1900]
	str r4, [r12, #748]
	ldr r4, [r12, #1904]
	str r4, [r12, #752]
	ldr r4, [r12, #1908]
	str r4, [r12, #756]
	ldr r4, [r12, #1912]
	str r4, [r12, #760]
	ldr r4, [r12, #1916]
	str r4, [r12, #764]
	ldr r4, [r12, #1920]
	str r4, [r12, #768]
	ldr r4, [r12, #1924]
	str r4, [r12, #772]
	ldr r4, [r12, #1928]
	str r4, [r12, #776]
	ldr r4, [r12, #1932]
	str r4, [r12, #780]
	ldr r4, [r12, #2128]
	str r4, [r12, #784]
	ldr r4, [r12, #2132]
	str r4, [r12, #788]
	ldr r4, [r12, #2136]
	str r4, [r12, #792]
	ldr r4, [r12, #2140]
	str r4, [r12, #796]
	ldr r4, [r12, #2144]
	str r4, [r12, #800]
	ldr r4, [r12, #2148]
	str r4, [r12, #804]
	ldr r4, [r12, #2152]
	str r4, [r12, #808]
	ldr r4, [r12, #2156]
	str r4, [r12, #812]
	ldr r4, [r12, #2160]
	str r4, [r12, #816]
	ldr r4, [r12, #2164]
	str r4, [r12, #820]
	ldr r4, [r12, #2168]
	str r4, [r12, #824]
	ldr r4, [r12, #2172]
	str r4, [r12, #828]
	mov r10, lr
	mov r0, r12
	bl {vg_p384_mul}
	mov lr, r10
	ldr r4, [r12, #304]
	str r4, [r12, #1456]
	ldr r4, [r12, #308]
	str r4, [r12, #1460]
	ldr r4, [r12, #312]
	str r4, [r12, #1464]
	ldr r4, [r12, #316]
	str r4, [r12, #1468]
	ldr r4, [r12, #320]
	str r4, [r12, #1472]
	ldr r4, [r12, #324]
	str r4, [r12, #1476]
	ldr r4, [r12, #328]
	str r4, [r12, #1480]
	ldr r4, [r12, #332]
	str r4, [r12, #1484]
	ldr r4, [r12, #336]
	str r4, [r12, #1488]
	ldr r4, [r12, #340]
	str r4, [r12, #1492]
	ldr r4, [r12, #344]
	str r4, [r12, #1496]
	ldr r4, [r12, #348]
	str r4, [r12, #1500]
	mov r11, #384
24:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #1456
	movw r2, #1456
	movw r3, #1456
	bl {vg_p384_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1504
	movw r2, #1456
	movw r3, #832
	bl {vg_p384_mul_mod_p}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #384]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #1456]
	ldr r5, [r12, #1504]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1456]
	ldr r4, [r12, #1460]
	ldr r5, [r12, #1508]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1460]
	ldr r4, [r12, #1464]
	ldr r5, [r12, #1512]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1464]
	ldr r4, [r12, #1468]
	ldr r5, [r12, #1516]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1468]
	ldr r4, [r12, #1472]
	ldr r5, [r12, #1520]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1472]
	ldr r4, [r12, #1476]
	ldr r5, [r12, #1524]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1476]
	ldr r4, [r12, #1480]
	ldr r5, [r12, #1528]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1480]
	ldr r4, [r12, #1484]
	ldr r5, [r12, #1532]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1484]
	ldr r4, [r12, #1488]
	ldr r5, [r12, #1536]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1488]
	ldr r4, [r12, #1492]
	ldr r5, [r12, #1540]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1492]
	ldr r4, [r12, #1496]
	ldr r5, [r12, #1544]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1496]
	ldr r4, [r12, #1500]
	ldr r5, [r12, #1548]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1500]
	cmp r11, #0
	bne 24b
	mov r10, lr
	mov r0, r12
	movw r1, #1696
	movw r2, #736
	movw r3, #1456
	bl {vg_p384_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1696
	movw r3, #256
	bl {vg_p384_mul_mod_p}
	mov lr, r10
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1600]
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
	ldr r7, [r12, #1604]
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
	ldr r7, [r12, #1608]
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
	ldr r7, [r12, #1612]
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
	ldr r7, [r12, #1616]
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
	ldr r7, [r12, #1620]
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
	ldr r7, [r12, #1624]
	ldr r8, [r12, #136]
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
	ldr r7, [r12, #1628]
	ldr r8, [r12, #140]
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
	ldr r7, [r12, #1632]
	ldr r8, [r12, #144]
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
	ldr r7, [r12, #1636]
	ldr r8, [r12, #148]
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
	ldr r7, [r12, #1640]
	ldr r8, [r12, #152]
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
	ldr r7, [r12, #1644]
	ldr r8, [r12, #156]
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
	ldr r5, [r12, #1600]
	ldr r4, [r12, #1604]
	orr r5, r5, r4
	ldr r4, [r12, #1608]
	orr r5, r5, r4
	ldr r4, [r12, #1612]
	orr r5, r5, r4
	ldr r4, [r12, #1616]
	orr r5, r5, r4
	ldr r4, [r12, #1620]
	orr r5, r5, r4
	ldr r4, [r12, #1624]
	orr r5, r5, r4
	ldr r4, [r12, #1628]
	orr r5, r5, r4
	ldr r4, [r12, #1632]
	orr r5, r5, r4
	ldr r4, [r12, #1636]
	orr r5, r5, r4
	ldr r4, [r12, #1640]
	orr r5, r5, r4
	ldr r4, [r12, #1644]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	and r5, r5, r9
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
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
	ldr r4, [r12, #856]
	orr r5, r5, r4
	ldr r4, [r12, #860]
	orr r5, r5, r4
	ldr r4, [r12, #864]
	orr r5, r5, r4
	ldr r4, [r12, #868]
	orr r5, r5, r4
	ldr r4, [r12, #872]
	orr r5, r5, r4
	ldr r4, [r12, #876]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	ldr r10, [r12, #2176]
	ldr r4, [r12, #1744]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #44]
	ldr r4, [r12, #1748]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #40]
	ldr r4, [r12, #1752]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #36]
	ldr r4, [r12, #1756]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #32]
	ldr r4, [r12, #1760]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #28]
	ldr r4, [r12, #1764]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #24]
	ldr r4, [r12, #1768]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #20]
	ldr r4, [r12, #1772]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #16]
	ldr r4, [r12, #1776]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #12]
	ldr r4, [r12, #1780]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #8]
	ldr r4, [r12, #1784]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #4]
	ldr r4, [r12, #1788]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #0]
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

vg_ecdh_p384_umaal:
	mov r12, r3
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
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #1552]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #1556]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1560]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1564]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1568]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1572]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1576]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1580]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1584]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1588]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1592]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1596]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #1600]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #1604]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1608]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1612]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1616]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1620]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1624]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1628]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1632]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1636]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1640]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1644]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #1648]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #1652]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1656]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1660]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1664]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1668]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1672]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1676]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1680]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1684]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1688]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1692]
	movw r10, #:lower16:({VG_P384_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P384_FRAME_CONSTS}
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
	add r10, r10, #48
	add r9, r9, #48
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #2176]
	mov r11, #48
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #1552]
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
	mov r11, #48
22:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #640]
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
	bne 22b
	mov r11, #48
23:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #688]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #768]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #769]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #770]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #771]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #772]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #773]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #774]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #775]
	cmp r11, #0
	bne 23b
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1936]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #1940]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1944]
	movw r4, #2
	movt r4, #0
	str r4, [r12, #1948]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1952]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #1956]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1960]
	movw r4, #2
	movt r4, #0
	str r4, [r12, #1964]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1968]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1972]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1976]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1980]
	movw r4, #11724
	movt r4, #40257
	str r4, [r12, #1984]
	movw r4, #34929
	movt r4, #2065
	str r4, [r12, #1988]
	movw r4, #13036
	movt r4, #31308
	str r4, [r12, #1992]
	movw r4, #44504
	movt r4, #63273
	str r4, [r12, #1996]
	movw r4, #558
	movt r4, #6432
	str r4, [r12, #2000]
	movw r4, #8347
	movt r4, #30706
	str r4, [r12, #2004]
	movw r4, #35554
	movt r4, #38035
	str r4, [r12, #2008]
	movw r4, #19438
	movt r4, #58167
	str r4, [r12, #2012]
	movw r4, #8340
	movt r4, #7938
	str r4, [r12, #2016]
	movw r4, #8692
	movt r4, #46635
	str r4, [r12, #2020]
	movw r4, #49145
	movt r4, #24655
	str r4, [r12, #2024]
	movw r4, #4427
	movt r4, #52488
	str r4, [r12, #2028]
	add r6, r2, #1
	ldr r4, [r6, #44]
	rev r4, r4
	str r4, [r12, #1648]
	ldr r4, [r6, #40]
	rev r4, r4
	str r4, [r12, #1652]
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #1656]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #1660]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1664]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1668]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1672]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1676]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1680]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1684]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1688]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1692]
	add r6, r6, #48
	ldr r4, [r6, #44]
	rev r4, r4
	str r4, [r12, #1792]
	ldr r4, [r6, #40]
	rev r4, r4
	str r4, [r12, #1796]
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #1800]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #1804]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1808]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1812]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1816]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1820]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1824]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1828]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1832]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1836]
	ldrb r4, [r2, #0]
	eor r4, r4, #4
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1648]
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
	ldr r7, [r12, #1652]
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
	ldr r7, [r12, #1656]
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
	ldr r7, [r12, #1660]
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
	ldr r7, [r12, #1664]
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
	ldr r7, [r12, #1668]
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
	ldr r7, [r12, #1672]
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
	ldr r7, [r12, #1676]
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
	ldr r7, [r12, #1680]
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
	ldr r7, [r12, #1684]
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
	ldr r7, [r12, #1688]
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
	ldr r7, [r12, #1692]
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
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1792]
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
	ldr r7, [r12, #1796]
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
	ldr r7, [r12, #1800]
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
	ldr r7, [r12, #1804]
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
	ldr r7, [r12, #1808]
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
	ldr r7, [r12, #1812]
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
	ldr r7, [r12, #1816]
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
	ldr r7, [r12, #1820]
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
	ldr r7, [r12, #1824]
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
	ldr r7, [r12, #1828]
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
	ldr r7, [r12, #1832]
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
	ldr r7, [r12, #1836]
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
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	mov r10, lr
	mov r0, r12
	movw r1, #1696
	movw r2, #1648
	movw r3, #1936
	bl {vg_p384_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1792
	movw r3, #1936
	bl {vg_p384_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1840
	movw r2, #1744
	movw r3, #1744
	bl {vg_p384_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #1696
	movw r3, #1696
	bl {vg_p384_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2080
	movw r2, #2032
	movw r3, #1696
	bl {vg_p384_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #352
	movw r3, #1696
	bl {vg_p384_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1888
	movw r2, #2080
	movw r3, #2032
	bl {vg_p384_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2080
	movw r2, #1888
	movw r3, #1984
	bl {vg_p384_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #1840
	movw r3, #2080
	bl {vg_p384_sub_mod_p_umaal}
	mov lr, r10
	ldr r5, [r12, #2032]
	ldr r4, [r12, #2036]
	orr r5, r5, r4
	ldr r4, [r12, #2040]
	orr r5, r5, r4
	ldr r4, [r12, #2044]
	orr r5, r5, r4
	ldr r4, [r12, #2048]
	orr r5, r5, r4
	ldr r4, [r12, #2052]
	orr r5, r5, r4
	ldr r4, [r12, #2056]
	orr r5, r5, r4
	ldr r4, [r12, #2060]
	orr r5, r5, r4
	ldr r4, [r12, #2064]
	orr r5, r5, r4
	ldr r4, [r12, #2068]
	orr r5, r5, r4
	ldr r4, [r12, #2072]
	orr r5, r5, r4
	ldr r4, [r12, #2076]
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
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	ldr r10, [r12, #2176]
	ldr r4, [r12, #448]
	ldr r5, [r12, #1696]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1888]
	ldr r4, [r12, #452]
	ldr r5, [r12, #1700]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1892]
	ldr r4, [r12, #456]
	ldr r5, [r12, #1704]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1896]
	ldr r4, [r12, #460]
	ldr r5, [r12, #1708]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1900]
	ldr r4, [r12, #464]
	ldr r5, [r12, #1712]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1904]
	ldr r4, [r12, #468]
	ldr r5, [r12, #1716]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1908]
	ldr r4, [r12, #472]
	ldr r5, [r12, #1720]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1912]
	ldr r4, [r12, #476]
	ldr r5, [r12, #1724]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1916]
	ldr r4, [r12, #480]
	ldr r5, [r12, #1728]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1920]
	ldr r4, [r12, #484]
	ldr r5, [r12, #1732]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1924]
	ldr r4, [r12, #488]
	ldr r5, [r12, #1736]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1928]
	ldr r4, [r12, #492]
	ldr r5, [r12, #1740]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1932]
	ldr r4, [r12, #496]
	ldr r5, [r12, #1744]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2128]
	ldr r4, [r12, #500]
	ldr r5, [r12, #1748]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2132]
	ldr r4, [r12, #504]
	ldr r5, [r12, #1752]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2136]
	ldr r4, [r12, #508]
	ldr r5, [r12, #1756]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2140]
	ldr r4, [r12, #512]
	ldr r5, [r12, #1760]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2144]
	ldr r4, [r12, #516]
	ldr r5, [r12, #1764]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2148]
	ldr r4, [r12, #520]
	ldr r5, [r12, #1768]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2152]
	ldr r4, [r12, #524]
	ldr r5, [r12, #1772]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2156]
	ldr r4, [r12, #528]
	ldr r5, [r12, #1776]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2160]
	ldr r4, [r12, #532]
	ldr r5, [r12, #1780]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2164]
	ldr r4, [r12, #536]
	ldr r5, [r12, #1784]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2168]
	ldr r4, [r12, #540]
	ldr r5, [r12, #1788]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #2172]
	ldr r4, [r12, #1888]
	str r4, [r12, #736]
	ldr r4, [r12, #1892]
	str r4, [r12, #740]
	ldr r4, [r12, #1896]
	str r4, [r12, #744]
	ldr r4, [r12, #1900]
	str r4, [r12, #748]
	ldr r4, [r12, #1904]
	str r4, [r12, #752]
	ldr r4, [r12, #1908]
	str r4, [r12, #756]
	ldr r4, [r12, #1912]
	str r4, [r12, #760]
	ldr r4, [r12, #1916]
	str r4, [r12, #764]
	ldr r4, [r12, #1920]
	str r4, [r12, #768]
	ldr r4, [r12, #1924]
	str r4, [r12, #772]
	ldr r4, [r12, #1928]
	str r4, [r12, #776]
	ldr r4, [r12, #1932]
	str r4, [r12, #780]
	ldr r4, [r12, #2128]
	str r4, [r12, #784]
	ldr r4, [r12, #2132]
	str r4, [r12, #788]
	ldr r4, [r12, #2136]
	str r4, [r12, #792]
	ldr r4, [r12, #2140]
	str r4, [r12, #796]
	ldr r4, [r12, #2144]
	str r4, [r12, #800]
	ldr r4, [r12, #2148]
	str r4, [r12, #804]
	ldr r4, [r12, #2152]
	str r4, [r12, #808]
	ldr r4, [r12, #2156]
	str r4, [r12, #812]
	ldr r4, [r12, #2160]
	str r4, [r12, #816]
	ldr r4, [r12, #2164]
	str r4, [r12, #820]
	ldr r4, [r12, #2168]
	str r4, [r12, #824]
	ldr r4, [r12, #2172]
	str r4, [r12, #828]
	mov r10, lr
	mov r0, r12
	bl {vg_p384_mul_umaal}
	mov lr, r10
	ldr r4, [r12, #304]
	str r4, [r12, #1456]
	ldr r4, [r12, #308]
	str r4, [r12, #1460]
	ldr r4, [r12, #312]
	str r4, [r12, #1464]
	ldr r4, [r12, #316]
	str r4, [r12, #1468]
	ldr r4, [r12, #320]
	str r4, [r12, #1472]
	ldr r4, [r12, #324]
	str r4, [r12, #1476]
	ldr r4, [r12, #328]
	str r4, [r12, #1480]
	ldr r4, [r12, #332]
	str r4, [r12, #1484]
	ldr r4, [r12, #336]
	str r4, [r12, #1488]
	ldr r4, [r12, #340]
	str r4, [r12, #1492]
	ldr r4, [r12, #344]
	str r4, [r12, #1496]
	ldr r4, [r12, #348]
	str r4, [r12, #1500]
	mov r11, #384
24:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #1456
	movw r2, #1456
	movw r3, #1456
	bl {vg_p384_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1504
	movw r2, #1456
	movw r3, #832
	bl {vg_p384_mul_mod_p_umaal}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #384]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #1456]
	ldr r5, [r12, #1504]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1456]
	ldr r4, [r12, #1460]
	ldr r5, [r12, #1508]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1460]
	ldr r4, [r12, #1464]
	ldr r5, [r12, #1512]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1464]
	ldr r4, [r12, #1468]
	ldr r5, [r12, #1516]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1468]
	ldr r4, [r12, #1472]
	ldr r5, [r12, #1520]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1472]
	ldr r4, [r12, #1476]
	ldr r5, [r12, #1524]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1476]
	ldr r4, [r12, #1480]
	ldr r5, [r12, #1528]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1480]
	ldr r4, [r12, #1484]
	ldr r5, [r12, #1532]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1484]
	ldr r4, [r12, #1488]
	ldr r5, [r12, #1536]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1488]
	ldr r4, [r12, #1492]
	ldr r5, [r12, #1540]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1492]
	ldr r4, [r12, #1496]
	ldr r5, [r12, #1544]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1496]
	ldr r4, [r12, #1500]
	ldr r5, [r12, #1548]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1500]
	cmp r11, #0
	bne 24b
	mov r10, lr
	mov r0, r12
	movw r1, #1696
	movw r2, #736
	movw r3, #1456
	bl {vg_p384_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1696
	movw r3, #256
	bl {vg_p384_mul_mod_p_umaal}
	mov lr, r10
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1600]
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
	ldr r7, [r12, #1604]
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
	ldr r7, [r12, #1608]
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
	ldr r7, [r12, #1612]
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
	ldr r7, [r12, #1616]
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
	ldr r7, [r12, #1620]
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
	ldr r7, [r12, #1624]
	ldr r8, [r12, #136]
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
	ldr r7, [r12, #1628]
	ldr r8, [r12, #140]
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
	ldr r7, [r12, #1632]
	ldr r8, [r12, #144]
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
	ldr r7, [r12, #1636]
	ldr r8, [r12, #148]
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
	ldr r7, [r12, #1640]
	ldr r8, [r12, #152]
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
	ldr r7, [r12, #1644]
	ldr r8, [r12, #156]
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
	ldr r5, [r12, #1600]
	ldr r4, [r12, #1604]
	orr r5, r5, r4
	ldr r4, [r12, #1608]
	orr r5, r5, r4
	ldr r4, [r12, #1612]
	orr r5, r5, r4
	ldr r4, [r12, #1616]
	orr r5, r5, r4
	ldr r4, [r12, #1620]
	orr r5, r5, r4
	ldr r4, [r12, #1624]
	orr r5, r5, r4
	ldr r4, [r12, #1628]
	orr r5, r5, r4
	ldr r4, [r12, #1632]
	orr r5, r5, r4
	ldr r4, [r12, #1636]
	orr r5, r5, r4
	ldr r4, [r12, #1640]
	orr r5, r5, r4
	ldr r4, [r12, #1644]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	and r5, r5, r9
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
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
	ldr r4, [r12, #856]
	orr r5, r5, r4
	ldr r4, [r12, #860]
	orr r5, r5, r4
	ldr r4, [r12, #864]
	orr r5, r5, r4
	ldr r4, [r12, #868]
	orr r5, r5, r4
	ldr r4, [r12, #872]
	orr r5, r5, r4
	ldr r4, [r12, #876]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	ldr r10, [r12, #2176]
	ldr r4, [r12, #1744]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #44]
	ldr r4, [r12, #1748]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #40]
	ldr r4, [r12, #1752]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #36]
	ldr r4, [r12, #1756]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #32]
	ldr r4, [r12, #1760]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #28]
	ldr r4, [r12, #1764]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #24]
	ldr r4, [r12, #1768]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #20]
	ldr r4, [r12, #1772]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #16]
	ldr r4, [r12, #1776]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #12]
	ldr r4, [r12, #1780]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #8]
	ldr r4, [r12, #1784]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #4]
	ldr r4, [r12, #1788]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #0]
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
