// The functions of `src/hmac_md5.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_md5_init:
	subs r12, r3, #65
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	bne 20f
	sub sp, sp, #416
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
	str r4, [r12, #112]
	str r5, [r12, #116]
	str r6, [r12, #120]
	str r7, [r12, #124]
	str r8, [r12, #128]
	str r9, [r12, #132]
	str r10, [r12, #136]
	str lr, [r12, #140]
	str r11, [r12, #144]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	mov r11, r12
	mov r0, r4
	bl {vg_md5_init}
	mov r0, r5
	bl {vg_md5_init}
	movw r1, #13878
	movt r1, #13878
	str r1, [r4, #16]
	str r1, [r4, #20]
	str r1, [r4, #24]
	str r1, [r4, #28]
	str r1, [r4, #32]
	str r1, [r4, #36]
	str r1, [r4, #40]
	str r1, [r4, #44]
	str r1, [r4, #48]
	str r1, [r4, #52]
	str r1, [r4, #56]
	str r1, [r4, #60]
	str r1, [r4, #64]
	str r1, [r4, #68]
	str r1, [r4, #72]
	str r1, [r4, #76]
	mov r8, r4
	cmp r7, #0
	beq 22f
24:
	ldrb r12, [r6, #0]
	eor r12, r12, #54
	strb r12, [r8, #16]
	add r6, r6, #1
	add r8, r8, #1
	subs r7, r7, #1
	bne 24b
	b 23f
22:
23:
	movw r1, #27242
	movt r1, #27242
	ldr r12, [r4, #16]
	eor r12, r12, r1
	str r12, [r5, #16]
	ldr r12, [r4, #20]
	eor r12, r12, r1
	str r12, [r5, #20]
	ldr r12, [r4, #24]
	eor r12, r12, r1
	str r12, [r5, #24]
	ldr r12, [r4, #28]
	eor r12, r12, r1
	str r12, [r5, #28]
	ldr r12, [r4, #32]
	eor r12, r12, r1
	str r12, [r5, #32]
	ldr r12, [r4, #36]
	eor r12, r12, r1
	str r12, [r5, #36]
	ldr r12, [r4, #40]
	eor r12, r12, r1
	str r12, [r5, #40]
	ldr r12, [r4, #44]
	eor r12, r12, r1
	str r12, [r5, #44]
	ldr r12, [r4, #48]
	eor r12, r12, r1
	str r12, [r5, #48]
	ldr r12, [r4, #52]
	eor r12, r12, r1
	str r12, [r5, #52]
	ldr r12, [r4, #56]
	eor r12, r12, r1
	str r12, [r5, #56]
	ldr r12, [r4, #60]
	eor r12, r12, r1
	str r12, [r5, #60]
	ldr r12, [r4, #64]
	eor r12, r12, r1
	str r12, [r5, #64]
	ldr r12, [r4, #68]
	eor r12, r12, r1
	str r12, [r5, #68]
	ldr r12, [r4, #72]
	eor r12, r12, r1
	str r12, [r5, #72]
	ldr r12, [r4, #76]
	eor r12, r12, r1
	str r12, [r5, #76]
	mov r0, r4
	add r6, r4, #16
	mov r3, r11
	mov r1, r6
	mov r2, #1
	bl {vg_md5_compress}
	mov r0, r5
	add r6, r5, #16
	mov r1, r6
	mov r2, #1
	bl {vg_md5_compress}
	ldr r4, [r11, #112]
	ldr r5, [r11, #116]
	ldr r6, [r11, #120]
	ldr r7, [r11, #124]
	ldr r8, [r11, #128]
	ldr r9, [r11, #132]
	ldr r10, [r11, #136]
	ldr lr, [r11, #140]
	ldr r11, [r11, #144]
	add sp, sp, #416
21:
	bx lr
20:
	sub sp, sp, #1056
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
	str r4, [r12, #384]
	str r5, [r12, #388]
	str r6, [r12, #392]
	str r7, [r12, #396]
	str r8, [r12, #400]
	str r9, [r12, #404]
	str r10, [r12, #408]
	str lr, [r12, #412]
	str r11, [r12, #416]
	mov r11, r12
	mov r8, r2
	mov r9, r3
	mov r5, r0
	mov r6, r1
	subs r12, r9, #65
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 25f
	movw r12, #660
	add r4, r11, r12
	mov r0, r4
	bl {vg_md5_init}
	mov r0, r4
	mov r1, r8
	mov r7, r9
	mov r10, r11
	mov r2, #0
	mov r3, #0
	push {r1, r7, r10, r12}
	bl {vg_md5_update_scratch}
	ldr r1, [sp], #16
	mov r0, r4
	movw r12, #772
	add r1, r11, r12
	mov r12, r11
	mov r2, r9
	mov r3, #0
	push {r1, r12}
	bl {vg_md5_finalize_scratch}
	ldr r1, [sp], #8
	movw r12, #772
	add r2, r11, r12
	movw r3, #16
	b 26f
25:
	mov r2, r8
	mov r3, r9
26:
	mov r0, r5
	mov r1, r6
	mov r12, r11
	push {r12, lr}
	bl {vg_hmac_md5_init_scratch}
	ldr r12, [sp], #8
	ldr r4, [r11, #384]
	ldr r5, [r11, #388]
	ldr r6, [r11, #392]
	ldr r7, [r11, #396]
	ldr r8, [r11, #400]
	ldr r9, [r11, #404]
	ldr r10, [r11, #408]
	ldr lr, [r11, #412]
	ldr r11, [r11, #416]
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
	add sp, sp, #1056
	b 21b

vg_hmac_md5_finalize:
	sub sp, sp, #416
	add r12, sp, #0
	str lr, [r12, #8]
	ldr lr, [sp, #416]
	str lr, [r12, #0]
	add lr, sp, #12
	str lr, [r12, #4]
	ldr lr, [sp, #8]
	ldr r12, [sp, #4]
	str r4, [r12, #112]
	str r5, [r12, #116]
	str r6, [r12, #120]
	str r7, [r12, #124]
	str r8, [r12, #128]
	str r9, [r12, #132]
	str r10, [r12, #136]
	str lr, [r12, #140]
	str r11, [r12, #144]
	mov r5, r1
	ldr r7, [sp, #0]
	mov r11, r12
	movw r12, #164
	add r1, r11, r12
	mov r12, r11
	push {r1, r12}
	bl {vg_md5_finalize_scratch}
	ldr r1, [sp], #8
	mov r3, r11
	movw r12, #148
	add r0, r11, r12
	movw r12, #164
	add r6, r11, r12
	ldr r12, [r5, #0]
	str r12, [r0, #0]
	ldr r12, [r5, #4]
	str r12, [r0, #4]
	ldr r12, [r5, #8]
	str r12, [r0, #8]
	ldr r12, [r5, #12]
	str r12, [r0, #12]
	mov r12, #128
	str r12, [r6, #16]
	mov r12, #0
	str r12, [r6, #20]
	str r12, [r6, #24]
	str r12, [r6, #28]
	str r12, [r6, #32]
	str r12, [r6, #36]
	str r12, [r6, #40]
	str r12, [r6, #44]
	str r12, [r6, #48]
	str r12, [r6, #52]
	movw r12, #640
	movt r12, #0
	str r12, [r6, #56]
	movw r12, #0
	movt r12, #0
	str r12, [r6, #60]
	mov r1, r6
	mov r2, #1
	bl {vg_md5_compress}
	mov r6, r7
	ldr r9, [r0, #0]
	str r9, [r6, #0]
	ldr r9, [r0, #4]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	str r9, [r6, #8]
	ldr r9, [r0, #12]
	str r9, [r6, #12]
	ldr r4, [r11, #112]
	ldr r5, [r11, #116]
	ldr r6, [r11, #120]
	ldr r7, [r11, #124]
	ldr r8, [r11, #128]
	ldr r9, [r11, #132]
	ldr r10, [r11, #136]
	ldr lr, [r11, #140]
	ldr r11, [r11, #144]
	add sp, sp, #416
	bx lr
