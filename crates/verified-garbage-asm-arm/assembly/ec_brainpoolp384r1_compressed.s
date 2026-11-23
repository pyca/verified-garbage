// The functions of `src/ec_brainpoolp384r1_compressed.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp384r1_compress_public_key:
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
	movw r10, #:lower16:({VG_BRAINPOOLP384R1_FRAME_CONSTS}
	movt r10, #:upper16:({VG_BRAINPOOLP384R1_FRAME_CONSTS}
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
	movw r4, #19422
	movt r4, #16566
	str r4, [r12, #1936]
	movw r4, #61439
	movt r4, #2172
	str r4, [r12, #1940]
	movw r4, #55653
	movt r4, #15743
	str r4, [r12, #1944]
	movw r4, #33588
	movt r4, #21330
	str r4, [r12, #1948]
	movw r4, #2201
	movt r4, #51604
	str r4, [r12, #1952]
	movw r4, #63900
	movt r4, #36392
	str r4, [r12, #1956]
	movw r4, #54703
	movt r4, #39192
	str r4, [r12, #1960]
	movw r4, #401
	movt r4, #25108
	str r4, [r12, #1964]
	movw r4, #1324
	movt r4, #42366
	str r4, [r12, #1968]
	movw r4, #61243
	movt r4, #54726
	str r4, [r12, #1972]
	movw r4, #63554
	movt r4, #6029
	str r4, [r12, #1976]
	movw r4, #26755
	movt r4, #14015
	str r4, [r12, #1980]
	movw r4, #57709
	movt r4, #200
	str r4, [r12, #1984]
	movw r4, #65002
	movt r4, #7941
	str r4, [r12, #1988]
	movw r4, #4067
	movt r4, #8282
	str r4, [r12, #1992]
	movw r4, #63432
	movt r4, #13870
	str r4, [r12, #1996]
	movw r4, #28378
	movt r4, #63265
	str r4, [r12, #2000]
	movw r4, #22211
	movt r4, #52660
	str r4, [r12, #2004]
	movw r4, #65240
	movt r4, #65143
	str r4, [r12, #2008]
	movw r4, #14375
	movt r4, #5953
	str r4, [r12, #2012]
	movw r4, #9565
	movt r4, #53709
	str r4, [r12, #2016]
	movw r4, #22145
	movt r4, #11059
	str r4, [r12, #2020]
	movw r4, #34474
	movt r4, #59462
	str r4, [r12, #2024]
	movw r4, #52986
	movt r4, #17725
	str r4, [r12, #2028]
	add r6, r1, #1
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
	ldrb r4, [r1, #0]
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
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1792
	movw r3, #1936
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1840
	movw r2, #1744
	movw r3, #1744
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #1696
	movw r3, #1696
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2080
	movw r2, #2032
	movw r3, #1696
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #352
	movw r3, #1696
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1888
	movw r2, #2080
	movw r3, #2032
	bl {vg_brainpoolp384r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2080
	movw r2, #1888
	movw r3, #1984
	bl {vg_brainpoolp384r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #1840
	movw r3, #2080
	bl {vg_brainpoolp384r1_sub_mod_p}
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
	ldr r10, [r12, #2176]
	ldr r4, [r12, #1792]
	and r4, r4, #1
	orr r4, r4, #2
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #1648]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #1652]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
	ldr r4, [r12, #1656]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #1660]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #1664]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #1668]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #1672]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #1676]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #1680]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #1684]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #1688]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #1692]
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

vg_ec_brainpoolp384r1_decompress_public_key:
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
	movw r10, #:lower16:({VG_BRAINPOOLP384R1_FRAME_CONSTS}
	movt r10, #:upper16:({VG_BRAINPOOLP384R1_FRAME_CONSTS}
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
	movw r4, #19422
	movt r4, #16566
	str r4, [r12, #1936]
	movw r4, #61439
	movt r4, #2172
	str r4, [r12, #1940]
	movw r4, #55653
	movt r4, #15743
	str r4, [r12, #1944]
	movw r4, #33588
	movt r4, #21330
	str r4, [r12, #1948]
	movw r4, #2201
	movt r4, #51604
	str r4, [r12, #1952]
	movw r4, #63900
	movt r4, #36392
	str r4, [r12, #1956]
	movw r4, #54703
	movt r4, #39192
	str r4, [r12, #1960]
	movw r4, #401
	movt r4, #25108
	str r4, [r12, #1964]
	movw r4, #1324
	movt r4, #42366
	str r4, [r12, #1968]
	movw r4, #61243
	movt r4, #54726
	str r4, [r12, #1972]
	movw r4, #63554
	movt r4, #6029
	str r4, [r12, #1976]
	movw r4, #26755
	movt r4, #14015
	str r4, [r12, #1980]
	movw r4, #57709
	movt r4, #200
	str r4, [r12, #1984]
	movw r4, #65002
	movt r4, #7941
	str r4, [r12, #1988]
	movw r4, #4067
	movt r4, #8282
	str r4, [r12, #1992]
	movw r4, #63432
	movt r4, #13870
	str r4, [r12, #1996]
	movw r4, #28378
	movt r4, #63265
	str r4, [r12, #2000]
	movw r4, #22211
	movt r4, #52660
	str r4, [r12, #2004]
	movw r4, #65240
	movt r4, #65143
	str r4, [r12, #2008]
	movw r4, #14375
	movt r4, #5953
	str r4, [r12, #2012]
	movw r4, #9565
	movt r4, #53709
	str r4, [r12, #2016]
	movw r4, #22145
	movt r4, #11059
	str r4, [r12, #2020]
	movw r4, #34474
	movt r4, #59462
	str r4, [r12, #2024]
	movw r4, #52986
	movt r4, #17725
	str r4, [r12, #2028]
	add r6, r1, #1
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
	ldrb r4, [r1, #0]
	str r4, [r12, #1600]
	orr r4, r4, #1
	eor r4, r4, #3
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
	mov r10, lr
	mov r0, r12
	movw r1, #1696
	movw r2, #1648
	movw r3, #1936
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #1696
	movw r3, #1696
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2080
	movw r2, #2032
	movw r3, #1696
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #352
	movw r3, #1696
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1888
	movw r2, #2080
	movw r3, #2032
	bl {vg_brainpoolp384r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2080
	movw r2, #1888
	movw r3, #1984
	bl {vg_brainpoolp384r1_add_mod_p}
	mov lr, r10
	movw r4, #64277
	movt r4, #52289
	str r4, [r12, #640]
	movw r4, #49156
	movt r4, #25041
	str r4, [r12, #644]
	movw r4, #18076
	movt r4, #25607
	str r4, [r12, #648]
	movw r4, #59850
	movt r4, #60212
	str r4, [r12, #652]
	movw r4, #50248
	movt r4, #24557
	str r4, [r12, #656]
	movw r4, #30342
	movt r4, #1196
	str r4, [r12, #660]
	movw r4, #5549
	movt r4, #31573
	str r4, [r12, #664]
	movw r4, #56386
	movt r4, #50507
	str r4, [r12, #668]
	movw r4, #36983
	movt r4, #37945
	str r4, [r12, #672]
	movw r4, #23519
	movt r4, #983
	str r4, [r12, #676]
	movw r4, #6986
	movt r4, #43214
	str r4, [r12, #680]
	movw r4, #18336
	movt r4, #9006
	str r4, [r12, #684]
	mov r11, #48
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #640]
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
	bne 21b
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
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #1456
	movw r2, #1456
	movw r3, #1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1504
	movw r2, #1456
	movw r3, #2080
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #768]
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
	bne 22b
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1456
	movw r3, #256
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1840
	movw r2, #208
	movw r3, #1792
	bl {vg_brainpoolp384r1_sub_mod_p}
	mov lr, r10
	ldr r4, [r12, #1792]
	ldr r5, [r12, #1600]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	ldr r4, [r12, #1792]
	ldr r5, [r12, #1840]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1792]
	ldr r4, [r12, #1796]
	ldr r5, [r12, #1844]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1796]
	ldr r4, [r12, #1800]
	ldr r5, [r12, #1848]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1800]
	ldr r4, [r12, #1804]
	ldr r5, [r12, #1852]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1804]
	ldr r4, [r12, #1808]
	ldr r5, [r12, #1856]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1808]
	ldr r4, [r12, #1812]
	ldr r5, [r12, #1860]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1812]
	ldr r4, [r12, #1816]
	ldr r5, [r12, #1864]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1816]
	ldr r4, [r12, #1820]
	ldr r5, [r12, #1868]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1820]
	ldr r4, [r12, #1824]
	ldr r5, [r12, #1872]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1824]
	ldr r4, [r12, #1828]
	ldr r5, [r12, #1876]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1828]
	ldr r4, [r12, #1832]
	ldr r5, [r12, #1880]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1832]
	ldr r4, [r12, #1836]
	ldr r5, [r12, #1884]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1836]
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1792
	movw r3, #1936
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #1744
	movw r3, #1744
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1888
	movw r2, #2032
	movw r3, #2080
	bl {vg_brainpoolp384r1_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #1888]
	ldr r4, [r12, #1892]
	orr r5, r5, r4
	ldr r4, [r12, #1896]
	orr r5, r5, r4
	ldr r4, [r12, #1900]
	orr r5, r5, r4
	ldr r4, [r12, #1904]
	orr r5, r5, r4
	ldr r4, [r12, #1908]
	orr r5, r5, r4
	ldr r4, [r12, #1912]
	orr r5, r5, r4
	ldr r4, [r12, #1916]
	orr r5, r5, r4
	ldr r4, [r12, #1920]
	orr r5, r5, r4
	ldr r4, [r12, #1924]
	orr r5, r5, r4
	ldr r4, [r12, #1928]
	orr r5, r5, r4
	ldr r4, [r12, #1932]
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
	ldr r4, [r12, #1792]
	ldr r5, [r12, #1600]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	add r5, r10, #1
	mov r4, #0
	sub r5, r4, r5
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	ldr r10, [r12, #2176]
	mov r4, #4
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #1648]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #1652]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
	ldr r4, [r12, #1656]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #1660]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #1664]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #1668]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #1672]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #1676]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #1680]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #1684]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #1688]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #1692]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
	ldr r4, [r12, #1792]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #93]
	ldr r4, [r12, #1796]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #89]
	ldr r4, [r12, #1800]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #85]
	ldr r4, [r12, #1804]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #81]
	ldr r4, [r12, #1808]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #77]
	ldr r4, [r12, #1812]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #73]
	ldr r4, [r12, #1816]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #69]
	ldr r4, [r12, #1820]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #65]
	ldr r4, [r12, #1824]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #61]
	ldr r4, [r12, #1828]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #57]
	ldr r4, [r12, #1832]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #53]
	ldr r4, [r12, #1836]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #49]
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

vg_ec_brainpoolp384r1_compress_public_key_umaal:
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
	movw r10, #:lower16:({VG_BRAINPOOLP384R1_FRAME_CONSTS}
	movt r10, #:upper16:({VG_BRAINPOOLP384R1_FRAME_CONSTS}
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
	movw r4, #19422
	movt r4, #16566
	str r4, [r12, #1936]
	movw r4, #61439
	movt r4, #2172
	str r4, [r12, #1940]
	movw r4, #55653
	movt r4, #15743
	str r4, [r12, #1944]
	movw r4, #33588
	movt r4, #21330
	str r4, [r12, #1948]
	movw r4, #2201
	movt r4, #51604
	str r4, [r12, #1952]
	movw r4, #63900
	movt r4, #36392
	str r4, [r12, #1956]
	movw r4, #54703
	movt r4, #39192
	str r4, [r12, #1960]
	movw r4, #401
	movt r4, #25108
	str r4, [r12, #1964]
	movw r4, #1324
	movt r4, #42366
	str r4, [r12, #1968]
	movw r4, #61243
	movt r4, #54726
	str r4, [r12, #1972]
	movw r4, #63554
	movt r4, #6029
	str r4, [r12, #1976]
	movw r4, #26755
	movt r4, #14015
	str r4, [r12, #1980]
	movw r4, #57709
	movt r4, #200
	str r4, [r12, #1984]
	movw r4, #65002
	movt r4, #7941
	str r4, [r12, #1988]
	movw r4, #4067
	movt r4, #8282
	str r4, [r12, #1992]
	movw r4, #63432
	movt r4, #13870
	str r4, [r12, #1996]
	movw r4, #28378
	movt r4, #63265
	str r4, [r12, #2000]
	movw r4, #22211
	movt r4, #52660
	str r4, [r12, #2004]
	movw r4, #65240
	movt r4, #65143
	str r4, [r12, #2008]
	movw r4, #14375
	movt r4, #5953
	str r4, [r12, #2012]
	movw r4, #9565
	movt r4, #53709
	str r4, [r12, #2016]
	movw r4, #22145
	movt r4, #11059
	str r4, [r12, #2020]
	movw r4, #34474
	movt r4, #59462
	str r4, [r12, #2024]
	movw r4, #52986
	movt r4, #17725
	str r4, [r12, #2028]
	add r6, r1, #1
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
	ldrb r4, [r1, #0]
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
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1792
	movw r3, #1936
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1840
	movw r2, #1744
	movw r3, #1744
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #1696
	movw r3, #1696
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2080
	movw r2, #2032
	movw r3, #1696
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #352
	movw r3, #1696
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1888
	movw r2, #2080
	movw r3, #2032
	bl {vg_brainpoolp384r1_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2080
	movw r2, #1888
	movw r3, #1984
	bl {vg_brainpoolp384r1_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #1840
	movw r3, #2080
	bl {vg_brainpoolp384r1_sub_mod_p_umaal}
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
	ldr r10, [r12, #2176]
	ldr r4, [r12, #1792]
	and r4, r4, #1
	orr r4, r4, #2
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #1648]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #1652]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
	ldr r4, [r12, #1656]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #1660]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #1664]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #1668]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #1672]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #1676]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #1680]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #1684]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #1688]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #1692]
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

vg_ec_brainpoolp384r1_decompress_public_key_umaal:
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
	movw r10, #:lower16:({VG_BRAINPOOLP384R1_FRAME_CONSTS}
	movt r10, #:upper16:({VG_BRAINPOOLP384R1_FRAME_CONSTS}
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
	movw r4, #19422
	movt r4, #16566
	str r4, [r12, #1936]
	movw r4, #61439
	movt r4, #2172
	str r4, [r12, #1940]
	movw r4, #55653
	movt r4, #15743
	str r4, [r12, #1944]
	movw r4, #33588
	movt r4, #21330
	str r4, [r12, #1948]
	movw r4, #2201
	movt r4, #51604
	str r4, [r12, #1952]
	movw r4, #63900
	movt r4, #36392
	str r4, [r12, #1956]
	movw r4, #54703
	movt r4, #39192
	str r4, [r12, #1960]
	movw r4, #401
	movt r4, #25108
	str r4, [r12, #1964]
	movw r4, #1324
	movt r4, #42366
	str r4, [r12, #1968]
	movw r4, #61243
	movt r4, #54726
	str r4, [r12, #1972]
	movw r4, #63554
	movt r4, #6029
	str r4, [r12, #1976]
	movw r4, #26755
	movt r4, #14015
	str r4, [r12, #1980]
	movw r4, #57709
	movt r4, #200
	str r4, [r12, #1984]
	movw r4, #65002
	movt r4, #7941
	str r4, [r12, #1988]
	movw r4, #4067
	movt r4, #8282
	str r4, [r12, #1992]
	movw r4, #63432
	movt r4, #13870
	str r4, [r12, #1996]
	movw r4, #28378
	movt r4, #63265
	str r4, [r12, #2000]
	movw r4, #22211
	movt r4, #52660
	str r4, [r12, #2004]
	movw r4, #65240
	movt r4, #65143
	str r4, [r12, #2008]
	movw r4, #14375
	movt r4, #5953
	str r4, [r12, #2012]
	movw r4, #9565
	movt r4, #53709
	str r4, [r12, #2016]
	movw r4, #22145
	movt r4, #11059
	str r4, [r12, #2020]
	movw r4, #34474
	movt r4, #59462
	str r4, [r12, #2024]
	movw r4, #52986
	movt r4, #17725
	str r4, [r12, #2028]
	add r6, r1, #1
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
	ldrb r4, [r1, #0]
	str r4, [r12, #1600]
	orr r4, r4, #1
	eor r4, r4, #3
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
	mov r10, lr
	mov r0, r12
	movw r1, #1696
	movw r2, #1648
	movw r3, #1936
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #1696
	movw r3, #1696
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2080
	movw r2, #2032
	movw r3, #1696
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #352
	movw r3, #1696
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1888
	movw r2, #2080
	movw r3, #2032
	bl {vg_brainpoolp384r1_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2080
	movw r2, #1888
	movw r3, #1984
	bl {vg_brainpoolp384r1_add_mod_p_umaal}
	mov lr, r10
	movw r4, #64277
	movt r4, #52289
	str r4, [r12, #640]
	movw r4, #49156
	movt r4, #25041
	str r4, [r12, #644]
	movw r4, #18076
	movt r4, #25607
	str r4, [r12, #648]
	movw r4, #59850
	movt r4, #60212
	str r4, [r12, #652]
	movw r4, #50248
	movt r4, #24557
	str r4, [r12, #656]
	movw r4, #30342
	movt r4, #1196
	str r4, [r12, #660]
	movw r4, #5549
	movt r4, #31573
	str r4, [r12, #664]
	movw r4, #56386
	movt r4, #50507
	str r4, [r12, #668]
	movw r4, #36983
	movt r4, #37945
	str r4, [r12, #672]
	movw r4, #23519
	movt r4, #983
	str r4, [r12, #676]
	movw r4, #6986
	movt r4, #43214
	str r4, [r12, #680]
	movw r4, #18336
	movt r4, #9006
	str r4, [r12, #684]
	mov r11, #48
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #640]
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
	bne 21b
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
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #1456
	movw r2, #1456
	movw r3, #1456
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1504
	movw r2, #1456
	movw r3, #2080
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #768]
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
	bne 22b
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1456
	movw r3, #256
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1840
	movw r2, #208
	movw r3, #1792
	bl {vg_brainpoolp384r1_sub_mod_p_umaal}
	mov lr, r10
	ldr r4, [r12, #1792]
	ldr r5, [r12, #1600]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	ldr r4, [r12, #1792]
	ldr r5, [r12, #1840]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1792]
	ldr r4, [r12, #1796]
	ldr r5, [r12, #1844]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1796]
	ldr r4, [r12, #1800]
	ldr r5, [r12, #1848]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1800]
	ldr r4, [r12, #1804]
	ldr r5, [r12, #1852]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1804]
	ldr r4, [r12, #1808]
	ldr r5, [r12, #1856]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1808]
	ldr r4, [r12, #1812]
	ldr r5, [r12, #1860]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1812]
	ldr r4, [r12, #1816]
	ldr r5, [r12, #1864]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1816]
	ldr r4, [r12, #1820]
	ldr r5, [r12, #1868]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1820]
	ldr r4, [r12, #1824]
	ldr r5, [r12, #1872]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1824]
	ldr r4, [r12, #1828]
	ldr r5, [r12, #1876]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1828]
	ldr r4, [r12, #1832]
	ldr r5, [r12, #1880]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1832]
	ldr r4, [r12, #1836]
	ldr r5, [r12, #1884]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1836]
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1792
	movw r3, #1936
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2032
	movw r2, #1744
	movw r3, #1744
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1888
	movw r2, #2032
	movw r3, #2080
	bl {vg_brainpoolp384r1_sub_mod_p_umaal}
	mov lr, r10
	ldr r5, [r12, #1888]
	ldr r4, [r12, #1892]
	orr r5, r5, r4
	ldr r4, [r12, #1896]
	orr r5, r5, r4
	ldr r4, [r12, #1900]
	orr r5, r5, r4
	ldr r4, [r12, #1904]
	orr r5, r5, r4
	ldr r4, [r12, #1908]
	orr r5, r5, r4
	ldr r4, [r12, #1912]
	orr r5, r5, r4
	ldr r4, [r12, #1916]
	orr r5, r5, r4
	ldr r4, [r12, #1920]
	orr r5, r5, r4
	ldr r4, [r12, #1924]
	orr r5, r5, r4
	ldr r4, [r12, #1928]
	orr r5, r5, r4
	ldr r4, [r12, #1932]
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
	ldr r4, [r12, #1792]
	ldr r5, [r12, #1600]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	add r5, r10, #1
	mov r4, #0
	sub r5, r4, r5
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	ldr r10, [r12, #2176]
	mov r4, #4
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #1648]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #1652]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
	ldr r4, [r12, #1656]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #1660]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #1664]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #1668]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #1672]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #1676]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #1680]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #1684]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #1688]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #1692]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
	ldr r4, [r12, #1792]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #93]
	ldr r4, [r12, #1796]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #89]
	ldr r4, [r12, #1800]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #85]
	ldr r4, [r12, #1804]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #81]
	ldr r4, [r12, #1808]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #77]
	ldr r4, [r12, #1812]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #73]
	ldr r4, [r12, #1816]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #69]
	ldr r4, [r12, #1820]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #65]
	ldr r4, [r12, #1824]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #61]
	ldr r4, [r12, #1828]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #57]
	ldr r4, [r12, #1832]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #53]
	ldr r4, [r12, #1836]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #49]
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
