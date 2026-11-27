// The functions of `src/internal/vg_brainpoolp320r1_mul.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_mul:
	mov r12, r0
	str r4, [r12, #1864]
	str r5, [r12, #1868]
	str r6, [r12, #1872]
	str r7, [r12, #1876]
	str r8, [r12, #1880]
	str r9, [r12, #1884]
	str r11, [r12, #1892]
	str lr, [r12, #1896]
	mov lr, r10
	mov r11, #40
20:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #1304]
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
	bne 20b
	movw r5, #5056
	add r5, r12, r5
	ldr r4, [r12, #184]
	str r4, [r5, #0]
	ldr r4, [r12, #188]
	str r4, [r5, #4]
	ldr r4, [r12, #192]
	str r4, [r5, #8]
	ldr r4, [r12, #196]
	str r4, [r5, #12]
	ldr r4, [r12, #200]
	str r4, [r5, #16]
	ldr r4, [r12, #204]
	str r4, [r5, #20]
	ldr r4, [r12, #208]
	str r4, [r5, #24]
	ldr r4, [r12, #212]
	str r4, [r5, #28]
	ldr r4, [r12, #216]
	str r4, [r5, #32]
	ldr r4, [r12, #220]
	str r4, [r5, #36]
	ldr r4, [r12, #264]
	str r4, [r5, #40]
	ldr r4, [r12, #268]
	str r4, [r5, #44]
	ldr r4, [r12, #272]
	str r4, [r5, #48]
	ldr r4, [r12, #276]
	str r4, [r5, #52]
	ldr r4, [r12, #280]
	str r4, [r5, #56]
	ldr r4, [r12, #284]
	str r4, [r5, #60]
	ldr r4, [r12, #288]
	str r4, [r5, #64]
	ldr r4, [r12, #292]
	str r4, [r5, #68]
	ldr r4, [r12, #296]
	str r4, [r5, #72]
	ldr r4, [r12, #300]
	str r4, [r5, #76]
	ldr r4, [r12, #184]
	str r4, [r5, #80]
	ldr r4, [r12, #188]
	str r4, [r5, #84]
	ldr r4, [r12, #192]
	str r4, [r5, #88]
	ldr r4, [r12, #196]
	str r4, [r5, #92]
	ldr r4, [r12, #200]
	str r4, [r5, #96]
	ldr r4, [r12, #204]
	str r4, [r5, #100]
	ldr r4, [r12, #208]
	str r4, [r5, #104]
	ldr r4, [r12, #212]
	str r4, [r5, #108]
	ldr r4, [r12, #216]
	str r4, [r5, #112]
	ldr r4, [r12, #220]
	str r4, [r5, #116]
	ldr r4, [r12, #624]
	str r4, [r5, #120]
	ldr r4, [r12, #628]
	str r4, [r5, #124]
	ldr r4, [r12, #632]
	str r4, [r5, #128]
	ldr r4, [r12, #636]
	str r4, [r5, #132]
	ldr r4, [r12, #640]
	str r4, [r5, #136]
	ldr r4, [r12, #644]
	str r4, [r5, #140]
	ldr r4, [r12, #648]
	str r4, [r5, #144]
	ldr r4, [r12, #652]
	str r4, [r5, #148]
	ldr r4, [r12, #656]
	str r4, [r5, #152]
	ldr r4, [r12, #660]
	str r4, [r5, #156]
	ldr r4, [r12, #664]
	str r4, [r5, #160]
	ldr r4, [r12, #668]
	str r4, [r5, #164]
	ldr r4, [r12, #672]
	str r4, [r5, #168]
	ldr r4, [r12, #676]
	str r4, [r5, #172]
	ldr r4, [r12, #680]
	str r4, [r5, #176]
	ldr r4, [r12, #684]
	str r4, [r5, #180]
	ldr r4, [r12, #688]
	str r4, [r5, #184]
	ldr r4, [r12, #692]
	str r4, [r5, #188]
	ldr r4, [r12, #696]
	str r4, [r5, #192]
	ldr r4, [r12, #700]
	str r4, [r5, #196]
	ldr r4, [r12, #264]
	str r4, [r5, #200]
	ldr r4, [r12, #268]
	str r4, [r5, #204]
	ldr r4, [r12, #272]
	str r4, [r5, #208]
	ldr r4, [r12, #276]
	str r4, [r5, #212]
	ldr r4, [r12, #280]
	str r4, [r5, #216]
	ldr r4, [r12, #284]
	str r4, [r5, #220]
	ldr r4, [r12, #288]
	str r4, [r5, #224]
	ldr r4, [r12, #292]
	str r4, [r5, #228]
	ldr r4, [r12, #296]
	str r4, [r5, #232]
	ldr r4, [r12, #300]
	str r4, [r5, #236]
	ldr r4, [r12, #624]
	str r4, [r12, #744]
	ldr r4, [r12, #628]
	str r4, [r12, #748]
	ldr r4, [r12, #632]
	str r4, [r12, #752]
	ldr r4, [r12, #636]
	str r4, [r12, #756]
	ldr r4, [r12, #640]
	str r4, [r12, #760]
	ldr r4, [r12, #644]
	str r4, [r12, #764]
	ldr r4, [r12, #648]
	str r4, [r12, #768]
	ldr r4, [r12, #652]
	str r4, [r12, #772]
	ldr r4, [r12, #656]
	str r4, [r12, #776]
	ldr r4, [r12, #660]
	str r4, [r12, #780]
	ldr r4, [r12, #664]
	str r4, [r12, #784]
	ldr r4, [r12, #668]
	str r4, [r12, #788]
	ldr r4, [r12, #672]
	str r4, [r12, #792]
	ldr r4, [r12, #676]
	str r4, [r12, #796]
	ldr r4, [r12, #680]
	str r4, [r12, #800]
	ldr r4, [r12, #684]
	str r4, [r12, #804]
	ldr r4, [r12, #688]
	str r4, [r12, #808]
	ldr r4, [r12, #692]
	str r4, [r12, #812]
	ldr r4, [r12, #696]
	str r4, [r12, #816]
	ldr r4, [r12, #700]
	str r4, [r12, #820]
	ldr r4, [r12, #264]
	str r4, [r12, #824]
	ldr r4, [r12, #268]
	str r4, [r12, #828]
	ldr r4, [r12, #272]
	str r4, [r12, #832]
	ldr r4, [r12, #276]
	str r4, [r12, #836]
	ldr r4, [r12, #280]
	str r4, [r12, #840]
	ldr r4, [r12, #284]
	str r4, [r12, #844]
	ldr r4, [r12, #288]
	str r4, [r12, #848]
	ldr r4, [r12, #292]
	str r4, [r12, #852]
	ldr r4, [r12, #296]
	str r4, [r12, #856]
	ldr r4, [r12, #300]
	str r4, [r12, #860]
	mov r11, #1
21:
	mov r10, lr
	mov r0, r12
	movw r1, #984
	movw r2, #744
	movw r3, #624
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #784
	movw r3, #664
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #824
	movw r3, #264
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #744
	movw r3, #784
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #624
	movw r3, #664
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #984
	movw r3, #1024
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #744
	movw r3, #824
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #624
	movw r3, #264
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #1144
	movw r3, #1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #984
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #1144
	movw r3, #1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #784
	movw r3, #824
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #664
	movw r3, #264
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1184
	movw r3, #864
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #1024
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1184
	movw r3, #864
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #944
	movw r2, #304
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #344
	movw r3, #1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #944
	movw r2, #864
	movw r3, #944
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #1024
	movw r3, #944
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #944
	movw r2, #1024
	movw r3, #944
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #864
	movw r3, #944
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #984
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #1024
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #304
	movw r3, #1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #344
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #1024
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #984
	movw r3, #1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #304
	movw r3, #1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #1144
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #984
	movw r2, #1024
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #904
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #984
	movw r2, #1184
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #1104
	movw r3, #864
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #864
	movw r3, #984
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #984
	movw r2, #1104
	movw r3, #1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #944
	movw r2, #1184
	movw r3, #944
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #944
	movw r2, #944
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r4, #120
	mul r4, r4, r11
	movw r5, #5176
	add r5, r12, r5
	add r5, r5, r4
	ldr r4, [r12, #864]
	str r4, [r5, #0]
	ldr r4, [r12, #868]
	str r4, [r5, #4]
	ldr r4, [r12, #872]
	str r4, [r5, #8]
	ldr r4, [r12, #876]
	str r4, [r5, #12]
	ldr r4, [r12, #880]
	str r4, [r5, #16]
	ldr r4, [r12, #884]
	str r4, [r5, #20]
	ldr r4, [r12, #888]
	str r4, [r5, #24]
	ldr r4, [r12, #892]
	str r4, [r5, #28]
	ldr r4, [r12, #896]
	str r4, [r5, #32]
	ldr r4, [r12, #900]
	str r4, [r5, #36]
	ldr r4, [r12, #904]
	str r4, [r5, #40]
	ldr r4, [r12, #908]
	str r4, [r5, #44]
	ldr r4, [r12, #912]
	str r4, [r5, #48]
	ldr r4, [r12, #916]
	str r4, [r5, #52]
	ldr r4, [r12, #920]
	str r4, [r5, #56]
	ldr r4, [r12, #924]
	str r4, [r5, #60]
	ldr r4, [r12, #928]
	str r4, [r5, #64]
	ldr r4, [r12, #932]
	str r4, [r5, #68]
	ldr r4, [r12, #936]
	str r4, [r5, #72]
	ldr r4, [r12, #940]
	str r4, [r5, #76]
	ldr r4, [r12, #944]
	str r4, [r5, #80]
	ldr r4, [r12, #948]
	str r4, [r5, #84]
	ldr r4, [r12, #952]
	str r4, [r5, #88]
	ldr r4, [r12, #956]
	str r4, [r5, #92]
	ldr r4, [r12, #960]
	str r4, [r5, #96]
	ldr r4, [r12, #964]
	str r4, [r5, #100]
	ldr r4, [r12, #968]
	str r4, [r5, #104]
	ldr r4, [r12, #972]
	str r4, [r5, #108]
	ldr r4, [r12, #976]
	str r4, [r5, #112]
	ldr r4, [r12, #980]
	str r4, [r5, #116]
	ldr r4, [r12, #864]
	str r4, [r12, #744]
	ldr r4, [r12, #868]
	str r4, [r12, #748]
	ldr r4, [r12, #872]
	str r4, [r12, #752]
	ldr r4, [r12, #876]
	str r4, [r12, #756]
	ldr r4, [r12, #880]
	str r4, [r12, #760]
	ldr r4, [r12, #884]
	str r4, [r12, #764]
	ldr r4, [r12, #888]
	str r4, [r12, #768]
	ldr r4, [r12, #892]
	str r4, [r12, #772]
	ldr r4, [r12, #896]
	str r4, [r12, #776]
	ldr r4, [r12, #900]
	str r4, [r12, #780]
	ldr r4, [r12, #904]
	str r4, [r12, #784]
	ldr r4, [r12, #908]
	str r4, [r12, #788]
	ldr r4, [r12, #912]
	str r4, [r12, #792]
	ldr r4, [r12, #916]
	str r4, [r12, #796]
	ldr r4, [r12, #920]
	str r4, [r12, #800]
	ldr r4, [r12, #924]
	str r4, [r12, #804]
	ldr r4, [r12, #928]
	str r4, [r12, #808]
	ldr r4, [r12, #932]
	str r4, [r12, #812]
	ldr r4, [r12, #936]
	str r4, [r12, #816]
	ldr r4, [r12, #940]
	str r4, [r12, #820]
	ldr r4, [r12, #944]
	str r4, [r12, #824]
	ldr r4, [r12, #948]
	str r4, [r12, #828]
	ldr r4, [r12, #952]
	str r4, [r12, #832]
	ldr r4, [r12, #956]
	str r4, [r12, #836]
	ldr r4, [r12, #960]
	str r4, [r12, #840]
	ldr r4, [r12, #964]
	str r4, [r12, #844]
	ldr r4, [r12, #968]
	str r4, [r12, #848]
	ldr r4, [r12, #972]
	str r4, [r12, #852]
	ldr r4, [r12, #976]
	str r4, [r12, #856]
	ldr r4, [r12, #980]
	str r4, [r12, #860]
	add r11, r11, #1
	cmp r11, #15
	bne 21b
	ldr r4, [r12, #184]
	str r4, [r12, #624]
	ldr r4, [r12, #188]
	str r4, [r12, #628]
	ldr r4, [r12, #192]
	str r4, [r12, #632]
	ldr r4, [r12, #196]
	str r4, [r12, #636]
	ldr r4, [r12, #200]
	str r4, [r12, #640]
	ldr r4, [r12, #204]
	str r4, [r12, #644]
	ldr r4, [r12, #208]
	str r4, [r12, #648]
	ldr r4, [r12, #212]
	str r4, [r12, #652]
	ldr r4, [r12, #216]
	str r4, [r12, #656]
	ldr r4, [r12, #220]
	str r4, [r12, #660]
	ldr r4, [r12, #264]
	str r4, [r12, #664]
	ldr r4, [r12, #268]
	str r4, [r12, #668]
	ldr r4, [r12, #272]
	str r4, [r12, #672]
	ldr r4, [r12, #276]
	str r4, [r12, #676]
	ldr r4, [r12, #280]
	str r4, [r12, #680]
	ldr r4, [r12, #284]
	str r4, [r12, #684]
	ldr r4, [r12, #288]
	str r4, [r12, #688]
	ldr r4, [r12, #292]
	str r4, [r12, #692]
	ldr r4, [r12, #296]
	str r4, [r12, #696]
	ldr r4, [r12, #300]
	str r4, [r12, #700]
	ldr r4, [r12, #184]
	str r4, [r12, #704]
	ldr r4, [r12, #188]
	str r4, [r12, #708]
	ldr r4, [r12, #192]
	str r4, [r12, #712]
	ldr r4, [r12, #196]
	str r4, [r12, #716]
	ldr r4, [r12, #200]
	str r4, [r12, #720]
	ldr r4, [r12, #204]
	str r4, [r12, #724]
	ldr r4, [r12, #208]
	str r4, [r12, #728]
	ldr r4, [r12, #212]
	str r4, [r12, #732]
	ldr r4, [r12, #216]
	str r4, [r12, #736]
	ldr r4, [r12, #220]
	str r4, [r12, #740]
	mov r11, #80
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #744
	movw r2, #624
	movw r3, #704
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #984
	movw r2, #704
	movw r3, #704
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #664
	movw r3, #984
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #824
	movw r2, #704
	movw r3, #184
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #984
	movw r2, #744
	movw r3, #744
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #784
	movw r3, #784
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1024
	movw r3, #1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #744
	movw r3, #1024
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1104
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #984
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1104
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #824
	movw r3, #824
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #1144
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #304
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #984
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1184
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #1144
	movw r3, #1184
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #944
	movw r2, #784
	movw r3, #824
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #944
	movw r2, #944
	movw r3, #944
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #1144
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #864
	movw r3, #1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #864
	movw r3, #1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #1104
	movw r3, #864
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #1144
	movw r3, #904
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1064
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1064
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1064
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #904
	movw r3, #1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #984
	movw r2, #864
	movw r3, #864
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #904
	movw r3, #904
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1024
	movw r3, #1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #864
	movw r3, #1024
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1104
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #984
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1104
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #944
	movw r3, #944
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #1144
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #304
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #984
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1184
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #1144
	movw r3, #1184
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #824
	movw r2, #904
	movw r3, #944
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #824
	movw r2, #824
	movw r3, #824
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #744
	movw r2, #1144
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #744
	movw r2, #744
	movw r3, #1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #744
	movw r2, #744
	movw r3, #1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #1104
	movw r3, #744
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #1144
	movw r3, #784
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1064
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1064
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1064
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #784
	movw r3, #1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #984
	movw r2, #744
	movw r3, #744
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #784
	movw r3, #784
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1024
	movw r3, #1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #744
	movw r3, #1024
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1104
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #984
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1104
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #824
	movw r3, #824
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #1144
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #304
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #984
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1184
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #1144
	movw r3, #1184
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #944
	movw r2, #784
	movw r3, #824
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #944
	movw r2, #944
	movw r3, #944
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #1144
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #864
	movw r3, #1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #864
	movw r3, #1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #1104
	movw r3, #864
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #1144
	movw r3, #904
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1064
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1064
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1064
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #904
	movw r3, #1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #984
	movw r2, #864
	movw r3, #864
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #904
	movw r3, #904
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1024
	movw r3, #1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #864
	movw r3, #1024
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1104
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #984
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1104
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #944
	movw r3, #944
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #1144
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #304
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #984
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1184
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #1144
	movw r3, #1184
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #824
	movw r2, #904
	movw r3, #944
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #824
	movw r2, #824
	movw r3, #824
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #744
	movw r2, #1144
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #744
	movw r2, #744
	movw r3, #1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #744
	movw r2, #744
	movw r3, #1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #1104
	movw r3, #744
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #1144
	movw r3, #784
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1064
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1064
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #1064
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #784
	movw r3, #1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #624
	movw r2, #744
	movw r3, #824
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #984
	movw r2, #824
	movw r3, #824
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #984
	movw r3, #824
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #784
	movw r3, #184
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	ldr r5, [r12, #704]
	ldr r4, [r12, #708]
	orr r5, r5, r4
	ldr r4, [r12, #712]
	orr r5, r5, r4
	ldr r4, [r12, #716]
	orr r5, r5, r4
	ldr r4, [r12, #720]
	orr r5, r5, r4
	ldr r4, [r12, #724]
	orr r5, r5, r4
	ldr r4, [r12, #728]
	orr r5, r5, r4
	ldr r4, [r12, #732]
	orr r5, r5, r4
	ldr r4, [r12, #736]
	orr r5, r5, r4
	ldr r4, [r12, #740]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	mov r10, r5
	ldr r4, [r12, #264]
	ldr r5, [r12, #664]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #664]
	ldr r4, [r12, #268]
	ldr r5, [r12, #668]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #668]
	ldr r4, [r12, #272]
	ldr r5, [r12, #672]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #672]
	ldr r4, [r12, #276]
	ldr r5, [r12, #676]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #676]
	ldr r4, [r12, #280]
	ldr r5, [r12, #680]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #680]
	ldr r4, [r12, #284]
	ldr r5, [r12, #684]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #684]
	ldr r4, [r12, #288]
	ldr r5, [r12, #688]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #688]
	ldr r4, [r12, #292]
	ldr r5, [r12, #692]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #692]
	ldr r4, [r12, #296]
	ldr r5, [r12, #696]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #696]
	ldr r4, [r12, #300]
	ldr r5, [r12, #700]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #700]
	mov r4, #4
	mul r4, r4, r11
	add r4, r12, r4
	add r4, r4, #4096
	cmp r11, #79
	beq 23f
	mov r9, #0
	add r9, r9, r9
	ldrb r5, [r4, #3]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #2]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #1]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #0]
	add r9, r9, r5
	b 24f
23:
	mov r9, #0
	add r9, r9, r9
	ldrb r5, [r4, #3]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #2]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #1]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #0]
	add r9, r9, r5
24:
	movw r8, #5056
	add r8, r12, r8
	mov r7, #0
25:
	eor r10, r9, r7
	sub r10, r10, #1
	lsr r10, r10, #31
	mov r5, #0
	sub r10, r5, r10
	ldr r4, [r12, #864]
	ldr r5, [r8, #0]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #864]
	ldr r4, [r12, #868]
	ldr r5, [r8, #4]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #868]
	ldr r4, [r12, #872]
	ldr r5, [r8, #8]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #872]
	ldr r4, [r12, #876]
	ldr r5, [r8, #12]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #876]
	ldr r4, [r12, #880]
	ldr r5, [r8, #16]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #880]
	ldr r4, [r12, #884]
	ldr r5, [r8, #20]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #884]
	ldr r4, [r12, #888]
	ldr r5, [r8, #24]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #888]
	ldr r4, [r12, #892]
	ldr r5, [r8, #28]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #892]
	ldr r4, [r12, #896]
	ldr r5, [r8, #32]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #896]
	ldr r4, [r12, #900]
	ldr r5, [r8, #36]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #900]
	ldr r4, [r12, #904]
	ldr r5, [r8, #40]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #904]
	ldr r4, [r12, #908]
	ldr r5, [r8, #44]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #908]
	ldr r4, [r12, #912]
	ldr r5, [r8, #48]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #912]
	ldr r4, [r12, #916]
	ldr r5, [r8, #52]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #916]
	ldr r4, [r12, #920]
	ldr r5, [r8, #56]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #920]
	ldr r4, [r12, #924]
	ldr r5, [r8, #60]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #924]
	ldr r4, [r12, #928]
	ldr r5, [r8, #64]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #928]
	ldr r4, [r12, #932]
	ldr r5, [r8, #68]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #932]
	ldr r4, [r12, #936]
	ldr r5, [r8, #72]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #936]
	ldr r4, [r12, #940]
	ldr r5, [r8, #76]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #940]
	ldr r4, [r12, #944]
	ldr r5, [r8, #80]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #944]
	ldr r4, [r12, #948]
	ldr r5, [r8, #84]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #948]
	ldr r4, [r12, #952]
	ldr r5, [r8, #88]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #952]
	ldr r4, [r12, #956]
	ldr r5, [r8, #92]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #956]
	ldr r4, [r12, #960]
	ldr r5, [r8, #96]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #960]
	ldr r4, [r12, #964]
	ldr r5, [r8, #100]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #964]
	ldr r4, [r12, #968]
	ldr r5, [r8, #104]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #968]
	ldr r4, [r12, #972]
	ldr r5, [r8, #108]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #972]
	ldr r4, [r12, #976]
	ldr r5, [r8, #112]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #976]
	ldr r4, [r12, #980]
	ldr r5, [r8, #116]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #980]
	add r8, r8, #120
	add r7, r7, #1
	cmp r7, #16
	bne 25b
	mov r10, lr
	mov r0, r12
	movw r1, #984
	movw r2, #624
	movw r3, #864
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #664
	movw r3, #904
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #704
	movw r3, #944
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #624
	movw r3, #664
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #864
	movw r3, #904
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #984
	movw r3, #1024
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1104
	movw r2, #1104
	movw r3, #1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #624
	movw r3, #704
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #864
	movw r3, #944
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #1144
	movw r3, #1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #984
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #1144
	movw r3, #1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #664
	movw r3, #704
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #744
	movw r2, #904
	movw r3, #944
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1184
	movw r3, #744
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #744
	movw r2, #1024
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1184
	movw r3, #744
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #824
	movw r2, #304
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #744
	movw r2, #344
	movw r3, #1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #824
	movw r2, #744
	movw r3, #824
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #744
	movw r2, #1024
	movw r3, #824
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #824
	movw r2, #1024
	movw r3, #824
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #744
	movw r3, #824
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #984
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #1024
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #304
	movw r3, #1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #344
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #1024
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #984
	movw r3, #1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1064
	movw r2, #304
	movw r3, #1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1144
	movw r2, #1144
	movw r3, #1064
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #984
	movw r2, #1024
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #784
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #984
	movw r2, #1184
	movw r3, #1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #744
	movw r2, #1104
	movw r3, #744
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #744
	movw r2, #744
	movw r3, #984
	bl {vg_brainpoolp320r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #984
	movw r2, #1104
	movw r3, #1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #824
	movw r2, #1184
	movw r3, #824
	bl {vg_brainpoolp320r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #824
	movw r2, #824
	movw r3, #984
	bl {vg_brainpoolp320r1_add_mod_p}
	mov lr, r10
	ldr r4, [r12, #744]
	str r4, [r12, #624]
	ldr r4, [r12, #748]
	str r4, [r12, #628]
	ldr r4, [r12, #752]
	str r4, [r12, #632]
	ldr r4, [r12, #756]
	str r4, [r12, #636]
	ldr r4, [r12, #760]
	str r4, [r12, #640]
	ldr r4, [r12, #764]
	str r4, [r12, #644]
	ldr r4, [r12, #768]
	str r4, [r12, #648]
	ldr r4, [r12, #772]
	str r4, [r12, #652]
	ldr r4, [r12, #776]
	str r4, [r12, #656]
	ldr r4, [r12, #780]
	str r4, [r12, #660]
	ldr r4, [r12, #784]
	str r4, [r12, #664]
	ldr r4, [r12, #788]
	str r4, [r12, #668]
	ldr r4, [r12, #792]
	str r4, [r12, #672]
	ldr r4, [r12, #796]
	str r4, [r12, #676]
	ldr r4, [r12, #800]
	str r4, [r12, #680]
	ldr r4, [r12, #804]
	str r4, [r12, #684]
	ldr r4, [r12, #808]
	str r4, [r12, #688]
	ldr r4, [r12, #812]
	str r4, [r12, #692]
	ldr r4, [r12, #816]
	str r4, [r12, #696]
	ldr r4, [r12, #820]
	str r4, [r12, #700]
	ldr r4, [r12, #824]
	str r4, [r12, #704]
	ldr r4, [r12, #828]
	str r4, [r12, #708]
	ldr r4, [r12, #832]
	str r4, [r12, #712]
	ldr r4, [r12, #836]
	str r4, [r12, #716]
	ldr r4, [r12, #840]
	str r4, [r12, #720]
	ldr r4, [r12, #844]
	str r4, [r12, #724]
	ldr r4, [r12, #848]
	str r4, [r12, #728]
	ldr r4, [r12, #852]
	str r4, [r12, #732]
	ldr r4, [r12, #856]
	str r4, [r12, #736]
	ldr r4, [r12, #860]
	str r4, [r12, #740]
	cmp r11, #0
	bne 22b
	mov r10, lr
	ldr r4, [r12, #1864]
	ldr r5, [r12, #1868]
	ldr r6, [r12, #1872]
	ldr r7, [r12, #1876]
	ldr r8, [r12, #1880]
	ldr r9, [r12, #1884]
	ldr r11, [r12, #1892]
	ldr lr, [r12, #1896]
	bx lr
