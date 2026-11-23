// The functions of `src/ec_brainpoolp320r1_compressed.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp320r1_compress_public_key:
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
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1304]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1308]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1312]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1316]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1320]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1324]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1328]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1332]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1336]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1340]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1344]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1348]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1352]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1356]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1360]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1364]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1368]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1372]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1376]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1380]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1384]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1388]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1392]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1396]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1400]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1404]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1408]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1412]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1416]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1420]
	movw r10, #:lower16:({VG_BRAINPOOLP320R1_FRAME_CONSTS}
	movt r10, #:upper16:({VG_BRAINPOOLP320R1_FRAME_CONSTS}
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
	add r10, r10, #40
	add r9, r9, #40
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1824]
	movw r4, #21241
	movt r4, #29755
	str r4, [r12, #1624]
	movw r4, #59530
	movt r4, #39246
	str r4, [r12, #1628]
	movw r4, #30959
	movt r4, #36969
	str r4, [r12, #1632]
	movw r4, #35469
	movt r4, #49735
	str r4, [r12, #1636]
	movw r4, #46710
	movt r4, #12485
	str r4, [r12, #1640]
	movw r4, #34847
	movt r4, #8012
	str r4, [r12, #1644]
	movw r4, #54994
	movt r4, #58900
	str r4, [r12, #1648]
	movw r4, #43364
	movt r4, #21589
	str r4, [r12, #1652]
	movw r4, #37458
	movt r4, #27693
	str r4, [r12, #1656]
	movw r4, #47690
	movt r4, #41561
	str r4, [r12, #1660]
	movw r4, #56090
	movt r4, #49137
	str r4, [r12, #1664]
	movw r4, #22776
	movt r4, #51502
	str r4, [r12, #1668]
	movw r4, #31493
	movt r4, #8324
	str r4, [r12, #1672]
	movw r4, #48094
	movt r4, #5306
	str r4, [r12, #1676]
	movw r4, #36601
	movt r4, #38493
	str r4, [r12, #1680]
	movw r4, #57818
	movt r4, #6230
	str r4, [r12, #1684]
	movw r4, #269
	movt r4, #8861
	str r4, [r12, #1688]
	movw r4, #40050
	movt r4, #37242
	str r4, [r12, #1692]
	movw r4, #21352
	movt r4, #10632
	str r4, [r12, #1696]
	movw r4, #45002
	movt r4, #37686
	str r4, [r12, #1700]
	add r6, r1, #1
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #1384]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #1388]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1392]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1396]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1400]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1404]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1408]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1412]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1416]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1420]
	add r6, r6, #40
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #1504]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #1508]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1512]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1516]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1520]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1524]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1528]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1532]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1536]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1540]
	ldrb r4, [r1, #0]
	eor r4, r4, #4
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1384]
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
	ldr r7, [r12, #1388]
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
	ldr r7, [r12, #1392]
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
	ldr r7, [r12, #1396]
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
	ldr r7, [r12, #1400]
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
	ldr r7, [r12, #1404]
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
	ldr r7, [r12, #1408]
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
	ldr r7, [r12, #1412]
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
	ldr r7, [r12, #1416]
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
	ldr r7, [r12, #1420]
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
	sub r5, r3, #1
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1504]
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
	ldr r7, [r12, #1508]
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
	ldr r7, [r12, #1512]
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
	ldr r7, [r12, #1516]
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
	ldr r7, [r12, #1520]
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
	ldr r7, [r12, #1524]
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
	ldr r7, [r12, #1528]
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
	ldr r7, [r12, #1532]
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
	ldr r7, [r12, #1536]
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
	ldr r7, [r12, #1540]
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
	sub r5, r3, #1
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	mov r10, lr
	mov r0, r12
	movw r1, #1424
	movw r2, #1384
	movw r3, #1624
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1464
	movw r2, #1504
	movw r3, #1624
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1544
	movw r2, #1464
	movw r3, #1464
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1704
	movw r2, #1424
	movw r3, #1424
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1704
	movw r3, #1424
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1704
	movw r2, #304
	movw r3, #1424
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1584
	movw r2, #1744
	movw r3, #1704
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1584
	movw r3, #1664
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1704
	movw r2, #1544
	movw r3, #1744
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #1704]
	ldr r4, [r12, #1708]
	orr r5, r5, r4
	ldr r4, [r12, #1712]
	orr r5, r5, r4
	ldr r4, [r12, #1716]
	orr r5, r5, r4
	ldr r4, [r12, #1720]
	orr r5, r5, r4
	ldr r4, [r12, #1724]
	orr r5, r5, r4
	ldr r4, [r12, #1728]
	orr r5, r5, r4
	ldr r4, [r12, #1732]
	orr r5, r5, r4
	ldr r4, [r12, #1736]
	orr r5, r5, r4
	ldr r4, [r12, #1740]
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
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	ldr r10, [r12, #1824]
	ldr r4, [r12, #384]
	ldr r5, [r12, #1424]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1584]
	ldr r4, [r12, #388]
	ldr r5, [r12, #1428]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1588]
	ldr r4, [r12, #392]
	ldr r5, [r12, #1432]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1592]
	ldr r4, [r12, #396]
	ldr r5, [r12, #1436]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1596]
	ldr r4, [r12, #400]
	ldr r5, [r12, #1440]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1600]
	ldr r4, [r12, #404]
	ldr r5, [r12, #1444]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1604]
	ldr r4, [r12, #408]
	ldr r5, [r12, #1448]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1608]
	ldr r4, [r12, #412]
	ldr r5, [r12, #1452]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1612]
	ldr r4, [r12, #416]
	ldr r5, [r12, #1456]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1616]
	ldr r4, [r12, #420]
	ldr r5, [r12, #1460]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1620]
	ldr r4, [r12, #424]
	ldr r5, [r12, #1464]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1784]
	ldr r4, [r12, #428]
	ldr r5, [r12, #1468]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1788]
	ldr r4, [r12, #432]
	ldr r5, [r12, #1472]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1792]
	ldr r4, [r12, #436]
	ldr r5, [r12, #1476]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1796]
	ldr r4, [r12, #440]
	ldr r5, [r12, #1480]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1800]
	ldr r4, [r12, #444]
	ldr r5, [r12, #1484]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1804]
	ldr r4, [r12, #448]
	ldr r5, [r12, #1488]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1808]
	ldr r4, [r12, #452]
	ldr r5, [r12, #1492]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1812]
	ldr r4, [r12, #456]
	ldr r5, [r12, #1496]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1816]
	ldr r4, [r12, #460]
	ldr r5, [r12, #1500]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1820]
	ldr r10, [r12, #1824]
	ldr r4, [r12, #1504]
	and r4, r4, #1
	orr r4, r4, #2
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #1384]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #1388]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #1392]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #1396]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #1400]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #1404]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #1408]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #1412]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #1416]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #1420]
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

vg_ec_brainpoolp320r1_decompress_public_key:
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
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1304]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1308]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1312]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1316]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1320]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1324]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1328]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1332]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1336]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1340]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1344]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1348]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1352]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1356]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1360]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1364]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1368]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1372]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1376]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1380]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1384]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1388]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1392]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1396]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1400]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1404]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1408]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1412]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1416]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1420]
	movw r10, #:lower16:({VG_BRAINPOOLP320R1_FRAME_CONSTS}
	movt r10, #:upper16:({VG_BRAINPOOLP320R1_FRAME_CONSTS}
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
	add r10, r10, #40
	add r9, r9, #40
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1824]
	movw r4, #21241
	movt r4, #29755
	str r4, [r12, #1624]
	movw r4, #59530
	movt r4, #39246
	str r4, [r12, #1628]
	movw r4, #30959
	movt r4, #36969
	str r4, [r12, #1632]
	movw r4, #35469
	movt r4, #49735
	str r4, [r12, #1636]
	movw r4, #46710
	movt r4, #12485
	str r4, [r12, #1640]
	movw r4, #34847
	movt r4, #8012
	str r4, [r12, #1644]
	movw r4, #54994
	movt r4, #58900
	str r4, [r12, #1648]
	movw r4, #43364
	movt r4, #21589
	str r4, [r12, #1652]
	movw r4, #37458
	movt r4, #27693
	str r4, [r12, #1656]
	movw r4, #47690
	movt r4, #41561
	str r4, [r12, #1660]
	movw r4, #56090
	movt r4, #49137
	str r4, [r12, #1664]
	movw r4, #22776
	movt r4, #51502
	str r4, [r12, #1668]
	movw r4, #31493
	movt r4, #8324
	str r4, [r12, #1672]
	movw r4, #48094
	movt r4, #5306
	str r4, [r12, #1676]
	movw r4, #36601
	movt r4, #38493
	str r4, [r12, #1680]
	movw r4, #57818
	movt r4, #6230
	str r4, [r12, #1684]
	movw r4, #269
	movt r4, #8861
	str r4, [r12, #1688]
	movw r4, #40050
	movt r4, #37242
	str r4, [r12, #1692]
	movw r4, #21352
	movt r4, #10632
	str r4, [r12, #1696]
	movw r4, #45002
	movt r4, #37686
	str r4, [r12, #1700]
	add r6, r1, #1
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #1384]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #1388]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1392]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1396]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1400]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1404]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1408]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1412]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1416]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1420]
	ldrb r4, [r1, #0]
	str r4, [r12, #1344]
	orr r4, r4, #1
	eor r4, r4, #3
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1384]
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
	ldr r7, [r12, #1388]
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
	ldr r7, [r12, #1392]
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
	ldr r7, [r12, #1396]
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
	ldr r7, [r12, #1400]
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
	ldr r7, [r12, #1404]
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
	ldr r7, [r12, #1408]
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
	ldr r7, [r12, #1412]
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
	ldr r7, [r12, #1416]
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
	ldr r7, [r12, #1420]
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
	sub r5, r3, #1
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	mov r10, lr
	mov r0, r12
	movw r1, #1424
	movw r2, #1384
	movw r3, #1624
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1704
	movw r2, #1424
	movw r3, #1424
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1704
	movw r3, #1424
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1704
	movw r2, #304
	movw r3, #1424
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1584
	movw r2, #1744
	movw r3, #1704
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1584
	movw r3, #1664
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	movw r4, #52106
	movt r4, #31852
	str r4, [r12, #544]
	movw r4, #1196
	movt r4, #16181
	str r4, [r12, #548]
	movw r4, #64266
	movt r4, #7716
	str r4, [r12, #552]
	movw r4, #44667
	movt r4, #54244
	str r4, [r12, #556]
	movw r4, #891
	movt r4, #48573
	str r4, [r12, #560]
	movw r4, #62441
	movt r4, #32355
	str r4, [r12, #564]
	movw r4, #30745
	movt r4, #46208
	str r4, [r12, #568]
	movw r4, #7703
	movt r4, #63567
	str r4, [r12, #572]
	movw r4, #5101
	movt r4, #3503
	str r4, [r12, #576]
	movw r4, #37320
	movt r4, #13527
	str r4, [r12, #580]
	mov r11, #40
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #544]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #640]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #641]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #642]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #643]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #644]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #645]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #646]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #647]
	cmp r11, #0
	bne 21b
	ldr r4, [r12, #264]
	str r4, [r12, #1224]
	ldr r4, [r12, #268]
	str r4, [r12, #1228]
	ldr r4, [r12, #272]
	str r4, [r12, #1232]
	ldr r4, [r12, #276]
	str r4, [r12, #1236]
	ldr r4, [r12, #280]
	str r4, [r12, #1240]
	ldr r4, [r12, #284]
	str r4, [r12, #1244]
	ldr r4, [r12, #288]
	str r4, [r12, #1248]
	ldr r4, [r12, #292]
	str r4, [r12, #1252]
	ldr r4, [r12, #296]
	str r4, [r12, #1256]
	ldr r4, [r12, #300]
	str r4, [r12, #1260]
	mov r11, #320
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #1224
	movw r2, #1224
	movw r3, #1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1264
	movw r2, #1224
	movw r3, #1744
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #640]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #1224]
	ldr r5, [r12, #1264]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1224]
	ldr r4, [r12, #1228]
	ldr r5, [r12, #1268]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1228]
	ldr r4, [r12, #1232]
	ldr r5, [r12, #1272]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1232]
	ldr r4, [r12, #1236]
	ldr r5, [r12, #1276]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1236]
	ldr r4, [r12, #1240]
	ldr r5, [r12, #1280]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1240]
	ldr r4, [r12, #1244]
	ldr r5, [r12, #1284]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1244]
	ldr r4, [r12, #1248]
	ldr r5, [r12, #1288]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1248]
	ldr r4, [r12, #1252]
	ldr r5, [r12, #1292]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1252]
	ldr r4, [r12, #1256]
	ldr r5, [r12, #1296]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1256]
	ldr r4, [r12, #1260]
	ldr r5, [r12, #1300]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1260]
	cmp r11, #0
	bne 22b
	mov r10, lr
	mov r0, r12
	movw r1, #1504
	movw r2, #1224
	movw r3, #224
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1544
	movw r2, #184
	movw r3, #1504
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	ldr r4, [r12, #1504]
	ldr r5, [r12, #1344]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	ldr r4, [r12, #1504]
	ldr r5, [r12, #1544]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1504]
	ldr r4, [r12, #1508]
	ldr r5, [r12, #1548]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1508]
	ldr r4, [r12, #1512]
	ldr r5, [r12, #1552]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1512]
	ldr r4, [r12, #1516]
	ldr r5, [r12, #1556]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1516]
	ldr r4, [r12, #1520]
	ldr r5, [r12, #1560]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1520]
	ldr r4, [r12, #1524]
	ldr r5, [r12, #1564]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1524]
	ldr r4, [r12, #1528]
	ldr r5, [r12, #1568]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1528]
	ldr r4, [r12, #1532]
	ldr r5, [r12, #1572]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1532]
	ldr r4, [r12, #1536]
	ldr r5, [r12, #1576]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1536]
	ldr r4, [r12, #1540]
	ldr r5, [r12, #1580]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1540]
	mov r10, lr
	mov r0, r12
	movw r1, #1464
	movw r2, #1504
	movw r3, #1624
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1704
	movw r2, #1464
	movw r3, #1464
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1584
	movw r2, #1704
	movw r3, #1744
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #1584]
	ldr r4, [r12, #1588]
	orr r5, r5, r4
	ldr r4, [r12, #1592]
	orr r5, r5, r4
	ldr r4, [r12, #1596]
	orr r5, r5, r4
	ldr r4, [r12, #1600]
	orr r5, r5, r4
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
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	mov r4, #0
	sub r5, r4, r5
	sub r5, r5, #1
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	ldr r4, [r12, #1504]
	ldr r5, [r12, #1344]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	add r5, r10, #1
	mov r4, #0
	sub r5, r4, r5
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	ldr r10, [r12, #1824]
	mov r4, #4
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #1384]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #1388]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #1392]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #1396]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #1400]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #1404]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #1408]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #1412]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #1416]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #1420]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
	ldr r4, [r12, #1504]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #77]
	ldr r4, [r12, #1508]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #73]
	ldr r4, [r12, #1512]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #69]
	ldr r4, [r12, #1516]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #65]
	ldr r4, [r12, #1520]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #61]
	ldr r4, [r12, #1524]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #57]
	ldr r4, [r12, #1528]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #53]
	ldr r4, [r12, #1532]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #49]
	ldr r4, [r12, #1536]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #1540]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
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

vg_ec_brainpoolp320r1_compress_public_key_umaal:
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
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1304]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1308]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1312]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1316]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1320]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1324]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1328]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1332]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1336]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1340]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1344]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1348]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1352]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1356]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1360]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1364]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1368]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1372]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1376]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1380]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1384]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1388]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1392]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1396]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1400]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1404]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1408]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1412]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1416]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1420]
	movw r10, #:lower16:({VG_BRAINPOOLP320R1_FRAME_CONSTS}
	movt r10, #:upper16:({VG_BRAINPOOLP320R1_FRAME_CONSTS}
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
	add r10, r10, #40
	add r9, r9, #40
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1824]
	movw r4, #21241
	movt r4, #29755
	str r4, [r12, #1624]
	movw r4, #59530
	movt r4, #39246
	str r4, [r12, #1628]
	movw r4, #30959
	movt r4, #36969
	str r4, [r12, #1632]
	movw r4, #35469
	movt r4, #49735
	str r4, [r12, #1636]
	movw r4, #46710
	movt r4, #12485
	str r4, [r12, #1640]
	movw r4, #34847
	movt r4, #8012
	str r4, [r12, #1644]
	movw r4, #54994
	movt r4, #58900
	str r4, [r12, #1648]
	movw r4, #43364
	movt r4, #21589
	str r4, [r12, #1652]
	movw r4, #37458
	movt r4, #27693
	str r4, [r12, #1656]
	movw r4, #47690
	movt r4, #41561
	str r4, [r12, #1660]
	movw r4, #56090
	movt r4, #49137
	str r4, [r12, #1664]
	movw r4, #22776
	movt r4, #51502
	str r4, [r12, #1668]
	movw r4, #31493
	movt r4, #8324
	str r4, [r12, #1672]
	movw r4, #48094
	movt r4, #5306
	str r4, [r12, #1676]
	movw r4, #36601
	movt r4, #38493
	str r4, [r12, #1680]
	movw r4, #57818
	movt r4, #6230
	str r4, [r12, #1684]
	movw r4, #269
	movt r4, #8861
	str r4, [r12, #1688]
	movw r4, #40050
	movt r4, #37242
	str r4, [r12, #1692]
	movw r4, #21352
	movt r4, #10632
	str r4, [r12, #1696]
	movw r4, #45002
	movt r4, #37686
	str r4, [r12, #1700]
	add r6, r1, #1
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #1384]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #1388]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1392]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1396]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1400]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1404]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1408]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1412]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1416]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1420]
	add r6, r6, #40
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #1504]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #1508]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1512]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1516]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1520]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1524]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1528]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1532]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1536]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1540]
	ldrb r4, [r1, #0]
	eor r4, r4, #4
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1384]
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
	ldr r7, [r12, #1388]
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
	ldr r7, [r12, #1392]
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
	ldr r7, [r12, #1396]
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
	ldr r7, [r12, #1400]
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
	ldr r7, [r12, #1404]
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
	ldr r7, [r12, #1408]
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
	ldr r7, [r12, #1412]
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
	ldr r7, [r12, #1416]
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
	ldr r7, [r12, #1420]
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
	sub r5, r3, #1
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1504]
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
	ldr r7, [r12, #1508]
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
	ldr r7, [r12, #1512]
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
	ldr r7, [r12, #1516]
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
	ldr r7, [r12, #1520]
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
	ldr r7, [r12, #1524]
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
	ldr r7, [r12, #1528]
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
	ldr r7, [r12, #1532]
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
	ldr r7, [r12, #1536]
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
	ldr r7, [r12, #1540]
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
	sub r5, r3, #1
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	mov r10, lr
	mov r0, r12
	movw r1, #1424
	movw r2, #1384
	movw r3, #1624
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1464
	movw r2, #1504
	movw r3, #1624
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1544
	movw r2, #1464
	movw r3, #1464
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1704
	movw r2, #1424
	movw r3, #1424
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1704
	movw r3, #1424
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1704
	movw r2, #304
	movw r3, #1424
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1584
	movw r2, #1744
	movw r3, #1704
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1584
	movw r3, #1664
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1704
	movw r2, #1544
	movw r3, #1744
	bl {vg_brainpoolp320r1_sub_mod_p_umaal}
	mov lr, r10
	ldr r5, [r12, #1704]
	ldr r4, [r12, #1708]
	orr r5, r5, r4
	ldr r4, [r12, #1712]
	orr r5, r5, r4
	ldr r4, [r12, #1716]
	orr r5, r5, r4
	ldr r4, [r12, #1720]
	orr r5, r5, r4
	ldr r4, [r12, #1724]
	orr r5, r5, r4
	ldr r4, [r12, #1728]
	orr r5, r5, r4
	ldr r4, [r12, #1732]
	orr r5, r5, r4
	ldr r4, [r12, #1736]
	orr r5, r5, r4
	ldr r4, [r12, #1740]
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
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	ldr r10, [r12, #1824]
	ldr r4, [r12, #384]
	ldr r5, [r12, #1424]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1584]
	ldr r4, [r12, #388]
	ldr r5, [r12, #1428]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1588]
	ldr r4, [r12, #392]
	ldr r5, [r12, #1432]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1592]
	ldr r4, [r12, #396]
	ldr r5, [r12, #1436]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1596]
	ldr r4, [r12, #400]
	ldr r5, [r12, #1440]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1600]
	ldr r4, [r12, #404]
	ldr r5, [r12, #1444]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1604]
	ldr r4, [r12, #408]
	ldr r5, [r12, #1448]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1608]
	ldr r4, [r12, #412]
	ldr r5, [r12, #1452]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1612]
	ldr r4, [r12, #416]
	ldr r5, [r12, #1456]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1616]
	ldr r4, [r12, #420]
	ldr r5, [r12, #1460]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1620]
	ldr r4, [r12, #424]
	ldr r5, [r12, #1464]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1784]
	ldr r4, [r12, #428]
	ldr r5, [r12, #1468]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1788]
	ldr r4, [r12, #432]
	ldr r5, [r12, #1472]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1792]
	ldr r4, [r12, #436]
	ldr r5, [r12, #1476]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1796]
	ldr r4, [r12, #440]
	ldr r5, [r12, #1480]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1800]
	ldr r4, [r12, #444]
	ldr r5, [r12, #1484]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1804]
	ldr r4, [r12, #448]
	ldr r5, [r12, #1488]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1808]
	ldr r4, [r12, #452]
	ldr r5, [r12, #1492]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1812]
	ldr r4, [r12, #456]
	ldr r5, [r12, #1496]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1816]
	ldr r4, [r12, #460]
	ldr r5, [r12, #1500]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1820]
	ldr r10, [r12, #1824]
	ldr r4, [r12, #1504]
	and r4, r4, #1
	orr r4, r4, #2
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #1384]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #1388]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #1392]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #1396]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #1400]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #1404]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #1408]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #1412]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #1416]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #1420]
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

vg_ec_brainpoolp320r1_decompress_public_key_umaal:
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
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1304]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1308]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1312]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1316]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1320]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1324]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1328]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1332]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1336]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1340]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1344]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1348]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1352]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1356]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1360]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1364]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1368]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1372]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1376]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1380]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1384]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1388]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1392]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1396]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1400]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1404]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1408]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1412]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1416]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1420]
	movw r10, #:lower16:({VG_BRAINPOOLP320R1_FRAME_CONSTS}
	movt r10, #:upper16:({VG_BRAINPOOLP320R1_FRAME_CONSTS}
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
	add r10, r10, #40
	add r9, r9, #40
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1824]
	movw r4, #21241
	movt r4, #29755
	str r4, [r12, #1624]
	movw r4, #59530
	movt r4, #39246
	str r4, [r12, #1628]
	movw r4, #30959
	movt r4, #36969
	str r4, [r12, #1632]
	movw r4, #35469
	movt r4, #49735
	str r4, [r12, #1636]
	movw r4, #46710
	movt r4, #12485
	str r4, [r12, #1640]
	movw r4, #34847
	movt r4, #8012
	str r4, [r12, #1644]
	movw r4, #54994
	movt r4, #58900
	str r4, [r12, #1648]
	movw r4, #43364
	movt r4, #21589
	str r4, [r12, #1652]
	movw r4, #37458
	movt r4, #27693
	str r4, [r12, #1656]
	movw r4, #47690
	movt r4, #41561
	str r4, [r12, #1660]
	movw r4, #56090
	movt r4, #49137
	str r4, [r12, #1664]
	movw r4, #22776
	movt r4, #51502
	str r4, [r12, #1668]
	movw r4, #31493
	movt r4, #8324
	str r4, [r12, #1672]
	movw r4, #48094
	movt r4, #5306
	str r4, [r12, #1676]
	movw r4, #36601
	movt r4, #38493
	str r4, [r12, #1680]
	movw r4, #57818
	movt r4, #6230
	str r4, [r12, #1684]
	movw r4, #269
	movt r4, #8861
	str r4, [r12, #1688]
	movw r4, #40050
	movt r4, #37242
	str r4, [r12, #1692]
	movw r4, #21352
	movt r4, #10632
	str r4, [r12, #1696]
	movw r4, #45002
	movt r4, #37686
	str r4, [r12, #1700]
	add r6, r1, #1
	ldr r4, [r6, #36]
	rev r4, r4
	str r4, [r12, #1384]
	ldr r4, [r6, #32]
	rev r4, r4
	str r4, [r12, #1388]
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1392]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1396]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1400]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1404]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1408]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1412]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1416]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1420]
	ldrb r4, [r1, #0]
	str r4, [r12, #1344]
	orr r4, r4, #1
	eor r4, r4, #3
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1384]
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
	ldr r7, [r12, #1388]
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
	ldr r7, [r12, #1392]
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
	ldr r7, [r12, #1396]
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
	ldr r7, [r12, #1400]
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
	ldr r7, [r12, #1404]
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
	ldr r7, [r12, #1408]
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
	ldr r7, [r12, #1412]
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
	ldr r7, [r12, #1416]
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
	ldr r7, [r12, #1420]
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
	sub r5, r3, #1
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	mov r10, lr
	mov r0, r12
	movw r1, #1424
	movw r2, #1384
	movw r3, #1624
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1704
	movw r2, #1424
	movw r3, #1424
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1704
	movw r3, #1424
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1704
	movw r2, #304
	movw r3, #1424
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1584
	movw r2, #1744
	movw r3, #1704
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1584
	movw r3, #1664
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov lr, r10
	movw r4, #52106
	movt r4, #31852
	str r4, [r12, #544]
	movw r4, #1196
	movt r4, #16181
	str r4, [r12, #548]
	movw r4, #64266
	movt r4, #7716
	str r4, [r12, #552]
	movw r4, #44667
	movt r4, #54244
	str r4, [r12, #556]
	movw r4, #891
	movt r4, #48573
	str r4, [r12, #560]
	movw r4, #62441
	movt r4, #32355
	str r4, [r12, #564]
	movw r4, #30745
	movt r4, #46208
	str r4, [r12, #568]
	movw r4, #7703
	movt r4, #63567
	str r4, [r12, #572]
	movw r4, #5101
	movt r4, #3503
	str r4, [r12, #576]
	movw r4, #37320
	movt r4, #13527
	str r4, [r12, #580]
	mov r11, #40
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #544]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #640]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #641]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #642]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #643]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #644]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #645]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #646]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #647]
	cmp r11, #0
	bne 21b
	ldr r4, [r12, #264]
	str r4, [r12, #1224]
	ldr r4, [r12, #268]
	str r4, [r12, #1228]
	ldr r4, [r12, #272]
	str r4, [r12, #1232]
	ldr r4, [r12, #276]
	str r4, [r12, #1236]
	ldr r4, [r12, #280]
	str r4, [r12, #1240]
	ldr r4, [r12, #284]
	str r4, [r12, #1244]
	ldr r4, [r12, #288]
	str r4, [r12, #1248]
	ldr r4, [r12, #292]
	str r4, [r12, #1252]
	ldr r4, [r12, #296]
	str r4, [r12, #1256]
	ldr r4, [r12, #300]
	str r4, [r12, #1260]
	mov r11, #320
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #1224
	movw r2, #1224
	movw r3, #1224
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1264
	movw r2, #1224
	movw r3, #1744
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #640]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #1224]
	ldr r5, [r12, #1264]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1224]
	ldr r4, [r12, #1228]
	ldr r5, [r12, #1268]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1228]
	ldr r4, [r12, #1232]
	ldr r5, [r12, #1272]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1232]
	ldr r4, [r12, #1236]
	ldr r5, [r12, #1276]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1236]
	ldr r4, [r12, #1240]
	ldr r5, [r12, #1280]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1240]
	ldr r4, [r12, #1244]
	ldr r5, [r12, #1284]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1244]
	ldr r4, [r12, #1248]
	ldr r5, [r12, #1288]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1248]
	ldr r4, [r12, #1252]
	ldr r5, [r12, #1292]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1252]
	ldr r4, [r12, #1256]
	ldr r5, [r12, #1296]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1256]
	ldr r4, [r12, #1260]
	ldr r5, [r12, #1300]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1260]
	cmp r11, #0
	bne 22b
	mov r10, lr
	mov r0, r12
	movw r1, #1504
	movw r2, #1224
	movw r3, #224
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1544
	movw r2, #184
	movw r3, #1504
	bl {vg_brainpoolp320r1_sub_mod_p_umaal}
	mov lr, r10
	ldr r4, [r12, #1504]
	ldr r5, [r12, #1344]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	ldr r4, [r12, #1504]
	ldr r5, [r12, #1544]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1504]
	ldr r4, [r12, #1508]
	ldr r5, [r12, #1548]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1508]
	ldr r4, [r12, #1512]
	ldr r5, [r12, #1552]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1512]
	ldr r4, [r12, #1516]
	ldr r5, [r12, #1556]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1516]
	ldr r4, [r12, #1520]
	ldr r5, [r12, #1560]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1520]
	ldr r4, [r12, #1524]
	ldr r5, [r12, #1564]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1524]
	ldr r4, [r12, #1528]
	ldr r5, [r12, #1568]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1528]
	ldr r4, [r12, #1532]
	ldr r5, [r12, #1572]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1532]
	ldr r4, [r12, #1536]
	ldr r5, [r12, #1576]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1536]
	ldr r4, [r12, #1540]
	ldr r5, [r12, #1580]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1540]
	mov r10, lr
	mov r0, r12
	movw r1, #1464
	movw r2, #1504
	movw r3, #1624
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1704
	movw r2, #1464
	movw r3, #1464
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1584
	movw r2, #1704
	movw r3, #1744
	bl {vg_brainpoolp320r1_sub_mod_p_umaal}
	mov lr, r10
	ldr r5, [r12, #1584]
	ldr r4, [r12, #1588]
	orr r5, r5, r4
	ldr r4, [r12, #1592]
	orr r5, r5, r4
	ldr r4, [r12, #1596]
	orr r5, r5, r4
	ldr r4, [r12, #1600]
	orr r5, r5, r4
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
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	mov r4, #0
	sub r5, r4, r5
	sub r5, r5, #1
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	ldr r4, [r12, #1504]
	ldr r5, [r12, #1344]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	add r5, r10, #1
	mov r4, #0
	sub r5, r4, r5
	ldr r4, [r12, #1824]
	and r4, r4, r5
	str r4, [r12, #1824]
	ldr r10, [r12, #1824]
	mov r4, #4
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #1384]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #1388]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #1392]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #1396]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #1400]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #1404]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #1408]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #1412]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #1416]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #1420]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
	ldr r4, [r12, #1504]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #77]
	ldr r4, [r12, #1508]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #73]
	ldr r4, [r12, #1512]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #69]
	ldr r4, [r12, #1516]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #65]
	ldr r4, [r12, #1520]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #61]
	ldr r4, [r12, #1524]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #57]
	ldr r4, [r12, #1528]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #53]
	ldr r4, [r12, #1532]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #49]
	ldr r4, [r12, #1536]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #1540]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
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
