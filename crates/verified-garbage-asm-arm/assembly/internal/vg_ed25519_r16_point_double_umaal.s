// The functions of `src/internal/vg_ed25519_r16_point_double_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_r16_point_double_umaal:
	str r4, [r0, #1600]
	str r5, [r0, #1604]
	str r6, [r0, #1608]
	str r7, [r0, #1612]
	str r8, [r0, #1616]
	str r9, [r0, #1620]
	movw r6, #65535
	mov r8, #38
	mov r5, #0
	ldr r3, [r0, #128]
	add r3, r3, #262144
	sub r3, r3, #76
	ldr r2, [r0, #64]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #576]
	lsr r5, r3, #16
	ldr r3, [r0, #132]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #68]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #580]
	lsr r5, r3, #16
	ldr r3, [r0, #136]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #72]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #584]
	lsr r5, r3, #16
	ldr r3, [r0, #140]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #76]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #588]
	lsr r5, r3, #16
	ldr r3, [r0, #144]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #80]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #592]
	lsr r5, r3, #16
	ldr r3, [r0, #148]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #84]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #596]
	lsr r5, r3, #16
	ldr r3, [r0, #152]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #88]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #600]
	lsr r5, r3, #16
	ldr r3, [r0, #156]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #92]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #604]
	lsr r5, r3, #16
	ldr r3, [r0, #160]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #96]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #608]
	lsr r5, r3, #16
	ldr r3, [r0, #164]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #100]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #612]
	lsr r5, r3, #16
	ldr r3, [r0, #168]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #104]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #616]
	lsr r5, r3, #16
	ldr r3, [r0, #172]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #108]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #620]
	lsr r5, r3, #16
	ldr r3, [r0, #176]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #112]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #624]
	lsr r5, r3, #16
	ldr r3, [r0, #180]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #116]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #628]
	lsr r5, r3, #16
	ldr r3, [r0, #184]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #120]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #632]
	lsr r5, r3, #16
	ldr r3, [r0, #188]
	add r3, r3, #131072
	sub r3, r3, #4
	ldr r2, [r0, #124]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #636]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #576]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #576]
	lsr r5, r3, #16
	ldr r3, [r0, #580]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #580]
	lsr r5, r3, #16
	ldr r3, [r0, #584]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #584]
	lsr r5, r3, #16
	ldr r3, [r0, #588]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #588]
	lsr r5, r3, #16
	ldr r3, [r0, #592]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #592]
	lsr r5, r3, #16
	ldr r3, [r0, #596]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #596]
	lsr r5, r3, #16
	ldr r3, [r0, #600]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #600]
	lsr r5, r3, #16
	ldr r3, [r0, #604]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #604]
	lsr r5, r3, #16
	ldr r3, [r0, #608]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #608]
	lsr r5, r3, #16
	ldr r3, [r0, #612]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #612]
	lsr r5, r3, #16
	ldr r3, [r0, #616]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #616]
	lsr r5, r3, #16
	ldr r3, [r0, #620]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #620]
	lsr r5, r3, #16
	ldr r3, [r0, #624]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #624]
	lsr r5, r3, #16
	ldr r3, [r0, #628]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #628]
	lsr r5, r3, #16
	ldr r3, [r0, #632]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #632]
	lsr r5, r3, #16
	ldr r3, [r0, #636]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #636]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #576]
	add r3, r3, r5
	str r3, [r0, #576]
	movw r1, #576
	movw r2, #576
	movw r3, #576
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
	movw r6, #65535
	mov r8, #38
	mov r5, #0
	ldr r3, [r0, #128]
	ldr r2, [r0, #64]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #640]
	lsr r5, r3, #16
	ldr r3, [r0, #132]
	ldr r2, [r0, #68]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #644]
	lsr r5, r3, #16
	ldr r3, [r0, #136]
	ldr r2, [r0, #72]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #648]
	lsr r5, r3, #16
	ldr r3, [r0, #140]
	ldr r2, [r0, #76]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #652]
	lsr r5, r3, #16
	ldr r3, [r0, #144]
	ldr r2, [r0, #80]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #656]
	lsr r5, r3, #16
	ldr r3, [r0, #148]
	ldr r2, [r0, #84]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #660]
	lsr r5, r3, #16
	ldr r3, [r0, #152]
	ldr r2, [r0, #88]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #664]
	lsr r5, r3, #16
	ldr r3, [r0, #156]
	ldr r2, [r0, #92]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #668]
	lsr r5, r3, #16
	ldr r3, [r0, #160]
	ldr r2, [r0, #96]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #672]
	lsr r5, r3, #16
	ldr r3, [r0, #164]
	ldr r2, [r0, #100]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #676]
	lsr r5, r3, #16
	ldr r3, [r0, #168]
	ldr r2, [r0, #104]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #680]
	lsr r5, r3, #16
	ldr r3, [r0, #172]
	ldr r2, [r0, #108]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #684]
	lsr r5, r3, #16
	ldr r3, [r0, #176]
	ldr r2, [r0, #112]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #688]
	lsr r5, r3, #16
	ldr r3, [r0, #180]
	ldr r2, [r0, #116]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #692]
	lsr r5, r3, #16
	ldr r3, [r0, #184]
	ldr r2, [r0, #120]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #696]
	lsr r5, r3, #16
	ldr r3, [r0, #188]
	ldr r2, [r0, #124]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #700]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #640]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #640]
	lsr r5, r3, #16
	ldr r3, [r0, #644]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #644]
	lsr r5, r3, #16
	ldr r3, [r0, #648]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #648]
	lsr r5, r3, #16
	ldr r3, [r0, #652]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #652]
	lsr r5, r3, #16
	ldr r3, [r0, #656]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #656]
	lsr r5, r3, #16
	ldr r3, [r0, #660]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #660]
	lsr r5, r3, #16
	ldr r3, [r0, #664]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #664]
	lsr r5, r3, #16
	ldr r3, [r0, #668]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #668]
	lsr r5, r3, #16
	ldr r3, [r0, #672]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #672]
	lsr r5, r3, #16
	ldr r3, [r0, #676]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #676]
	lsr r5, r3, #16
	ldr r3, [r0, #680]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #680]
	lsr r5, r3, #16
	ldr r3, [r0, #684]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #684]
	lsr r5, r3, #16
	ldr r3, [r0, #688]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #688]
	lsr r5, r3, #16
	ldr r3, [r0, #692]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #692]
	lsr r5, r3, #16
	ldr r3, [r0, #696]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #696]
	lsr r5, r3, #16
	ldr r3, [r0, #700]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #700]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #640]
	add r3, r3, r5
	str r3, [r0, #640]
	movw r1, #640
	movw r2, #640
	movw r3, #640
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
	movw r1, #704
	movw r2, #256
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
	movw r6, #65535
	mov r8, #38
	mov r5, #0
	ldr r3, [r0, #704]
	ldr r2, [r0, #704]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #704]
	lsr r5, r3, #16
	ldr r3, [r0, #708]
	ldr r2, [r0, #708]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #708]
	lsr r5, r3, #16
	ldr r3, [r0, #712]
	ldr r2, [r0, #712]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #712]
	lsr r5, r3, #16
	ldr r3, [r0, #716]
	ldr r2, [r0, #716]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #716]
	lsr r5, r3, #16
	ldr r3, [r0, #720]
	ldr r2, [r0, #720]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #720]
	lsr r5, r3, #16
	ldr r3, [r0, #724]
	ldr r2, [r0, #724]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #724]
	lsr r5, r3, #16
	ldr r3, [r0, #728]
	ldr r2, [r0, #728]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #728]
	lsr r5, r3, #16
	ldr r3, [r0, #732]
	ldr r2, [r0, #732]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #732]
	lsr r5, r3, #16
	ldr r3, [r0, #736]
	ldr r2, [r0, #736]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #736]
	lsr r5, r3, #16
	ldr r3, [r0, #740]
	ldr r2, [r0, #740]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #740]
	lsr r5, r3, #16
	ldr r3, [r0, #744]
	ldr r2, [r0, #744]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #744]
	lsr r5, r3, #16
	ldr r3, [r0, #748]
	ldr r2, [r0, #748]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #748]
	lsr r5, r3, #16
	ldr r3, [r0, #752]
	ldr r2, [r0, #752]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #752]
	lsr r5, r3, #16
	ldr r3, [r0, #756]
	ldr r2, [r0, #756]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #756]
	lsr r5, r3, #16
	ldr r3, [r0, #760]
	ldr r2, [r0, #760]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #760]
	lsr r5, r3, #16
	ldr r3, [r0, #764]
	ldr r2, [r0, #764]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #764]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #704]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #704]
	lsr r5, r3, #16
	ldr r3, [r0, #708]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #708]
	lsr r5, r3, #16
	ldr r3, [r0, #712]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #712]
	lsr r5, r3, #16
	ldr r3, [r0, #716]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #716]
	lsr r5, r3, #16
	ldr r3, [r0, #720]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #720]
	lsr r5, r3, #16
	ldr r3, [r0, #724]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #724]
	lsr r5, r3, #16
	ldr r3, [r0, #728]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #728]
	lsr r5, r3, #16
	ldr r3, [r0, #732]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #732]
	lsr r5, r3, #16
	ldr r3, [r0, #736]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #736]
	lsr r5, r3, #16
	ldr r3, [r0, #740]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #740]
	lsr r5, r3, #16
	ldr r3, [r0, #744]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #744]
	lsr r5, r3, #16
	ldr r3, [r0, #748]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #748]
	lsr r5, r3, #16
	ldr r3, [r0, #752]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #752]
	lsr r5, r3, #16
	ldr r3, [r0, #756]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #756]
	lsr r5, r3, #16
	ldr r3, [r0, #760]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #760]
	lsr r5, r3, #16
	ldr r3, [r0, #764]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #764]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #704]
	add r3, r3, r5
	str r3, [r0, #704]
	movw r1, #704
	movw r2, #704
	movw r3, #256
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
	movw r6, #65535
	mov r8, #38
	mov r5, #0
	ldr r3, [r0, #192]
	ldr r2, [r0, #192]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #768]
	lsr r5, r3, #16
	ldr r3, [r0, #196]
	ldr r2, [r0, #196]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #772]
	lsr r5, r3, #16
	ldr r3, [r0, #200]
	ldr r2, [r0, #200]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #776]
	lsr r5, r3, #16
	ldr r3, [r0, #204]
	ldr r2, [r0, #204]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #780]
	lsr r5, r3, #16
	ldr r3, [r0, #208]
	ldr r2, [r0, #208]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #784]
	lsr r5, r3, #16
	ldr r3, [r0, #212]
	ldr r2, [r0, #212]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #788]
	lsr r5, r3, #16
	ldr r3, [r0, #216]
	ldr r2, [r0, #216]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #792]
	lsr r5, r3, #16
	ldr r3, [r0, #220]
	ldr r2, [r0, #220]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #796]
	lsr r5, r3, #16
	ldr r3, [r0, #224]
	ldr r2, [r0, #224]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #800]
	lsr r5, r3, #16
	ldr r3, [r0, #228]
	ldr r2, [r0, #228]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #804]
	lsr r5, r3, #16
	ldr r3, [r0, #232]
	ldr r2, [r0, #232]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #808]
	lsr r5, r3, #16
	ldr r3, [r0, #236]
	ldr r2, [r0, #236]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #812]
	lsr r5, r3, #16
	ldr r3, [r0, #240]
	ldr r2, [r0, #240]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #816]
	lsr r5, r3, #16
	ldr r3, [r0, #244]
	ldr r2, [r0, #244]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #820]
	lsr r5, r3, #16
	ldr r3, [r0, #248]
	ldr r2, [r0, #248]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #824]
	lsr r5, r3, #16
	ldr r3, [r0, #252]
	ldr r2, [r0, #252]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #828]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #768]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #768]
	lsr r5, r3, #16
	ldr r3, [r0, #772]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #772]
	lsr r5, r3, #16
	ldr r3, [r0, #776]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #776]
	lsr r5, r3, #16
	ldr r3, [r0, #780]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #780]
	lsr r5, r3, #16
	ldr r3, [r0, #784]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #784]
	lsr r5, r3, #16
	ldr r3, [r0, #788]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #788]
	lsr r5, r3, #16
	ldr r3, [r0, #792]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #792]
	lsr r5, r3, #16
	ldr r3, [r0, #796]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #796]
	lsr r5, r3, #16
	ldr r3, [r0, #800]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #800]
	lsr r5, r3, #16
	ldr r3, [r0, #804]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #804]
	lsr r5, r3, #16
	ldr r3, [r0, #808]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #808]
	lsr r5, r3, #16
	ldr r3, [r0, #812]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #812]
	lsr r5, r3, #16
	ldr r3, [r0, #816]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #816]
	lsr r5, r3, #16
	ldr r3, [r0, #820]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #820]
	lsr r5, r3, #16
	ldr r3, [r0, #824]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #824]
	lsr r5, r3, #16
	ldr r3, [r0, #828]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #828]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #768]
	add r3, r3, r5
	str r3, [r0, #768]
	movw r1, #768
	movw r2, #768
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
	movw r6, #65535
	mov r8, #38
	mov r5, #0
	ldr r3, [r0, #640]
	add r3, r3, #262144
	sub r3, r3, #76
	ldr r2, [r0, #576]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #832]
	lsr r5, r3, #16
	ldr r3, [r0, #644]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #580]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #836]
	lsr r5, r3, #16
	ldr r3, [r0, #648]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #584]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #840]
	lsr r5, r3, #16
	ldr r3, [r0, #652]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #588]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #844]
	lsr r5, r3, #16
	ldr r3, [r0, #656]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #592]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #848]
	lsr r5, r3, #16
	ldr r3, [r0, #660]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #596]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #852]
	lsr r5, r3, #16
	ldr r3, [r0, #664]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #600]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #856]
	lsr r5, r3, #16
	ldr r3, [r0, #668]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #604]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #860]
	lsr r5, r3, #16
	ldr r3, [r0, #672]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #608]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #864]
	lsr r5, r3, #16
	ldr r3, [r0, #676]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #612]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #868]
	lsr r5, r3, #16
	ldr r3, [r0, #680]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #616]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #872]
	lsr r5, r3, #16
	ldr r3, [r0, #684]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #620]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #876]
	lsr r5, r3, #16
	ldr r3, [r0, #688]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #624]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #880]
	lsr r5, r3, #16
	ldr r3, [r0, #692]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #628]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #884]
	lsr r5, r3, #16
	ldr r3, [r0, #696]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #632]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #888]
	lsr r5, r3, #16
	ldr r3, [r0, #700]
	add r3, r3, #131072
	sub r3, r3, #4
	ldr r2, [r0, #636]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #892]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #832]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #832]
	lsr r5, r3, #16
	ldr r3, [r0, #836]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #836]
	lsr r5, r3, #16
	ldr r3, [r0, #840]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #840]
	lsr r5, r3, #16
	ldr r3, [r0, #844]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #844]
	lsr r5, r3, #16
	ldr r3, [r0, #848]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #848]
	lsr r5, r3, #16
	ldr r3, [r0, #852]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #852]
	lsr r5, r3, #16
	ldr r3, [r0, #856]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #856]
	lsr r5, r3, #16
	ldr r3, [r0, #860]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #860]
	lsr r5, r3, #16
	ldr r3, [r0, #864]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #864]
	lsr r5, r3, #16
	ldr r3, [r0, #868]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #868]
	lsr r5, r3, #16
	ldr r3, [r0, #872]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #872]
	lsr r5, r3, #16
	ldr r3, [r0, #876]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #876]
	lsr r5, r3, #16
	ldr r3, [r0, #880]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #880]
	lsr r5, r3, #16
	ldr r3, [r0, #884]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #884]
	lsr r5, r3, #16
	ldr r3, [r0, #888]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #888]
	lsr r5, r3, #16
	ldr r3, [r0, #892]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #892]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #832]
	add r3, r3, r5
	str r3, [r0, #832]
	movw r6, #65535
	mov r8, #38
	mov r5, #0
	ldr r3, [r0, #768]
	add r3, r3, #262144
	sub r3, r3, #76
	ldr r2, [r0, #704]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #896]
	lsr r5, r3, #16
	ldr r3, [r0, #772]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #708]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #900]
	lsr r5, r3, #16
	ldr r3, [r0, #776]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #712]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #904]
	lsr r5, r3, #16
	ldr r3, [r0, #780]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #716]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #908]
	lsr r5, r3, #16
	ldr r3, [r0, #784]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #720]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #912]
	lsr r5, r3, #16
	ldr r3, [r0, #788]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #724]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #916]
	lsr r5, r3, #16
	ldr r3, [r0, #792]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #728]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #920]
	lsr r5, r3, #16
	ldr r3, [r0, #796]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #732]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #924]
	lsr r5, r3, #16
	ldr r3, [r0, #800]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #736]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #928]
	lsr r5, r3, #16
	ldr r3, [r0, #804]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #740]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #932]
	lsr r5, r3, #16
	ldr r3, [r0, #808]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #744]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #936]
	lsr r5, r3, #16
	ldr r3, [r0, #812]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #748]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #940]
	lsr r5, r3, #16
	ldr r3, [r0, #816]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #752]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #944]
	lsr r5, r3, #16
	ldr r3, [r0, #820]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #756]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #948]
	lsr r5, r3, #16
	ldr r3, [r0, #824]
	add r3, r3, #262144
	sub r3, r3, #4
	ldr r2, [r0, #760]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #952]
	lsr r5, r3, #16
	ldr r3, [r0, #828]
	add r3, r3, #131072
	sub r3, r3, #4
	ldr r2, [r0, #764]
	sub r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #956]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #896]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #896]
	lsr r5, r3, #16
	ldr r3, [r0, #900]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #900]
	lsr r5, r3, #16
	ldr r3, [r0, #904]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #904]
	lsr r5, r3, #16
	ldr r3, [r0, #908]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #908]
	lsr r5, r3, #16
	ldr r3, [r0, #912]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #912]
	lsr r5, r3, #16
	ldr r3, [r0, #916]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #916]
	lsr r5, r3, #16
	ldr r3, [r0, #920]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #920]
	lsr r5, r3, #16
	ldr r3, [r0, #924]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #924]
	lsr r5, r3, #16
	ldr r3, [r0, #928]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #928]
	lsr r5, r3, #16
	ldr r3, [r0, #932]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #932]
	lsr r5, r3, #16
	ldr r3, [r0, #936]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #936]
	lsr r5, r3, #16
	ldr r3, [r0, #940]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #940]
	lsr r5, r3, #16
	ldr r3, [r0, #944]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #944]
	lsr r5, r3, #16
	ldr r3, [r0, #948]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #948]
	lsr r5, r3, #16
	ldr r3, [r0, #952]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #952]
	lsr r5, r3, #16
	ldr r3, [r0, #956]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #956]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #896]
	add r3, r3, r5
	str r3, [r0, #896]
	movw r6, #65535
	mov r8, #38
	mov r5, #0
	ldr r3, [r0, #768]
	ldr r2, [r0, #704]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #960]
	lsr r5, r3, #16
	ldr r3, [r0, #772]
	ldr r2, [r0, #708]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #964]
	lsr r5, r3, #16
	ldr r3, [r0, #776]
	ldr r2, [r0, #712]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #968]
	lsr r5, r3, #16
	ldr r3, [r0, #780]
	ldr r2, [r0, #716]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #972]
	lsr r5, r3, #16
	ldr r3, [r0, #784]
	ldr r2, [r0, #720]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #976]
	lsr r5, r3, #16
	ldr r3, [r0, #788]
	ldr r2, [r0, #724]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #980]
	lsr r5, r3, #16
	ldr r3, [r0, #792]
	ldr r2, [r0, #728]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #984]
	lsr r5, r3, #16
	ldr r3, [r0, #796]
	ldr r2, [r0, #732]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #988]
	lsr r5, r3, #16
	ldr r3, [r0, #800]
	ldr r2, [r0, #736]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #992]
	lsr r5, r3, #16
	ldr r3, [r0, #804]
	ldr r2, [r0, #740]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #996]
	lsr r5, r3, #16
	ldr r3, [r0, #808]
	ldr r2, [r0, #744]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1000]
	lsr r5, r3, #16
	ldr r3, [r0, #812]
	ldr r2, [r0, #748]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1004]
	lsr r5, r3, #16
	ldr r3, [r0, #816]
	ldr r2, [r0, #752]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1008]
	lsr r5, r3, #16
	ldr r3, [r0, #820]
	ldr r2, [r0, #756]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1012]
	lsr r5, r3, #16
	ldr r3, [r0, #824]
	ldr r2, [r0, #760]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1016]
	lsr r5, r3, #16
	ldr r3, [r0, #828]
	ldr r2, [r0, #764]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1020]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #960]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #960]
	lsr r5, r3, #16
	ldr r3, [r0, #964]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #964]
	lsr r5, r3, #16
	ldr r3, [r0, #968]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #968]
	lsr r5, r3, #16
	ldr r3, [r0, #972]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #972]
	lsr r5, r3, #16
	ldr r3, [r0, #976]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #976]
	lsr r5, r3, #16
	ldr r3, [r0, #980]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #980]
	lsr r5, r3, #16
	ldr r3, [r0, #984]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #984]
	lsr r5, r3, #16
	ldr r3, [r0, #988]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #988]
	lsr r5, r3, #16
	ldr r3, [r0, #992]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #992]
	lsr r5, r3, #16
	ldr r3, [r0, #996]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #996]
	lsr r5, r3, #16
	ldr r3, [r0, #1000]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1000]
	lsr r5, r3, #16
	ldr r3, [r0, #1004]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1004]
	lsr r5, r3, #16
	ldr r3, [r0, #1008]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1008]
	lsr r5, r3, #16
	ldr r3, [r0, #1012]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1012]
	lsr r5, r3, #16
	ldr r3, [r0, #1016]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1016]
	lsr r5, r3, #16
	ldr r3, [r0, #1020]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1020]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #960]
	add r3, r3, r5
	str r3, [r0, #960]
	movw r6, #65535
	mov r8, #38
	mov r5, #0
	ldr r3, [r0, #640]
	ldr r2, [r0, #576]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1024]
	lsr r5, r3, #16
	ldr r3, [r0, #644]
	ldr r2, [r0, #580]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1028]
	lsr r5, r3, #16
	ldr r3, [r0, #648]
	ldr r2, [r0, #584]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1032]
	lsr r5, r3, #16
	ldr r3, [r0, #652]
	ldr r2, [r0, #588]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1036]
	lsr r5, r3, #16
	ldr r3, [r0, #656]
	ldr r2, [r0, #592]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1040]
	lsr r5, r3, #16
	ldr r3, [r0, #660]
	ldr r2, [r0, #596]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1044]
	lsr r5, r3, #16
	ldr r3, [r0, #664]
	ldr r2, [r0, #600]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1048]
	lsr r5, r3, #16
	ldr r3, [r0, #668]
	ldr r2, [r0, #604]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1052]
	lsr r5, r3, #16
	ldr r3, [r0, #672]
	ldr r2, [r0, #608]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1056]
	lsr r5, r3, #16
	ldr r3, [r0, #676]
	ldr r2, [r0, #612]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1060]
	lsr r5, r3, #16
	ldr r3, [r0, #680]
	ldr r2, [r0, #616]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1064]
	lsr r5, r3, #16
	ldr r3, [r0, #684]
	ldr r2, [r0, #620]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1068]
	lsr r5, r3, #16
	ldr r3, [r0, #688]
	ldr r2, [r0, #624]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1072]
	lsr r5, r3, #16
	ldr r3, [r0, #692]
	ldr r2, [r0, #628]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1076]
	lsr r5, r3, #16
	ldr r3, [r0, #696]
	ldr r2, [r0, #632]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1080]
	lsr r5, r3, #16
	ldr r3, [r0, #700]
	ldr r2, [r0, #636]
	add r3, r3, r2
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1084]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #1024]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1024]
	lsr r5, r3, #16
	ldr r3, [r0, #1028]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1028]
	lsr r5, r3, #16
	ldr r3, [r0, #1032]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1032]
	lsr r5, r3, #16
	ldr r3, [r0, #1036]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1036]
	lsr r5, r3, #16
	ldr r3, [r0, #1040]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1040]
	lsr r5, r3, #16
	ldr r3, [r0, #1044]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1044]
	lsr r5, r3, #16
	ldr r3, [r0, #1048]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1048]
	lsr r5, r3, #16
	ldr r3, [r0, #1052]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1052]
	lsr r5, r3, #16
	ldr r3, [r0, #1056]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1056]
	lsr r5, r3, #16
	ldr r3, [r0, #1060]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1060]
	lsr r5, r3, #16
	ldr r3, [r0, #1064]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1064]
	lsr r5, r3, #16
	ldr r3, [r0, #1068]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1068]
	lsr r5, r3, #16
	ldr r3, [r0, #1072]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1072]
	lsr r5, r3, #16
	ldr r3, [r0, #1076]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1076]
	lsr r5, r3, #16
	ldr r3, [r0, #1080]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1080]
	lsr r5, r3, #16
	ldr r3, [r0, #1084]
	add r3, r3, r5
	and r4, r3, r6
	str r4, [r0, #1084]
	lsr r5, r3, #16
	mul r5, r5, r8
	ldr r3, [r0, #1024]
	add r3, r3, r5
	str r3, [r0, #1024]
	movw r1, #64
	movw r2, #832
	movw r3, #896
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
	movw r1, #128
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
	movw r1, #192
	movw r2, #896
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
	movw r1, #256
	movw r2, #832
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
28:
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
	bne 28b
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
	bx lr
