// The functions of `src/ed448.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_public_key:
	push {lr}
	push {r12}
	sub sp, sp, #24
	sub sp, sp, #248
	add r12, sp, #248
	str r0, [r12, #0]
	add r12, sp, #248
	str r1, [r12, #4]
	add r12, sp, #248
	str r2, [r12, #8]
	ldr r0, [sp, #256]
	add r0, r0, #0
	movw r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	str r1, [r0, #8]
	str r1, [r0, #12]
	str r1, [r0, #16]
	str r1, [r0, #20]
	str r1, [r0, #24]
	str r1, [r0, #28]
	str r1, [r0, #32]
	str r1, [r0, #36]
	str r1, [r0, #40]
	str r1, [r0, #44]
	str r1, [r0, #48]
	str r1, [r0, #52]
	str r1, [r0, #56]
	str r1, [r0, #60]
	str r1, [r0, #64]
	str r1, [r0, #68]
	str r1, [r0, #72]
	str r1, [r0, #76]
	str r1, [r0, #80]
	str r1, [r0, #84]
	str r1, [r0, #88]
	str r1, [r0, #92]
	str r1, [r0, #96]
	str r1, [r0, #100]
	str r1, [r0, #104]
	str r1, [r0, #108]
	str r1, [r0, #112]
	str r1, [r0, #116]
	str r1, [r0, #120]
	str r1, [r0, #124]
	str r1, [r0, #128]
	str r1, [r0, #132]
	str r1, [r0, #136]
	str r1, [r0, #140]
	str r1, [r0, #144]
	str r1, [r0, #148]
	str r1, [r0, #152]
	str r1, [r0, #156]
	str r1, [r0, #160]
	str r1, [r0, #164]
	str r1, [r0, #168]
	str r1, [r0, #172]
	str r1, [r0, #176]
	str r1, [r0, #180]
	str r1, [r0, #184]
	str r1, [r0, #188]
	str r1, [r0, #192]
	str r1, [r0, #196]
	movw r0, #57
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #256]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #256]
	add r0, r0, #0
	movw r1, #136
	movw r2, #0
	ldr r3, [sp, #252]
	add r3, r3, #0
	bl {vg_keccak_absorb_scratch}
	ldr r0, [sp, #256]
	add r0, r0, #208
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #256]
	add r0, r0, #0
	movw r1, #136
	movw r2, #57
	movw r3, #31
	bl {vg_keccak_pad_scratch}
	movw r0, #114
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #256]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #256]
	add r0, r0, #0
	movw r1, #136
	movw r2, #0
	add r3, sp, #24
	bl {vg_keccak_squeeze_scratch}
	add r12, sp, #24
	ldrb r0, [r12, #0]
	and r0, r0, #252
	strb r0, [r12, #0]
	ldrb r0, [r12, #55]
	orr r0, r0, #128
	strb r0, [r12, #55]
	movw r0, #0
	strb r0, [r12, #56]
	ldr r0, [sp, #248]
	add r0, r0, #0
	add r1, sp, #24
	ldr r2, [sp, #256]
	add r2, r2, #0
	bl {vg_ed448_scalar_base}
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #24]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #28]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #32]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #36]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #40]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #44]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #48]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #52]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #56]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #60]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #64]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #68]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #72]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #76]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #80]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #84]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #88]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #96]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #100]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #104]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #108]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #112]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #116]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #120]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #128]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #132]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #136]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #140]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #144]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #148]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #152]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #156]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #160]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #164]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #168]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #172]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #176]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #180]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #184]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #188]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #192]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #196]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #200]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #204]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #208]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #212]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #216]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #220]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #224]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #228]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #232]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #236]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #240]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #244]
	add sp, sp, #248
	add sp, sp, #24
	ldr r12, [sp], #4
	ldr lr, [sp], #4
	bx lr

vg_ed448_sign_cached:
	push {lr}
	push {r12}
	sub sp, sp, #24
	sub sp, sp, #248
	add r12, sp, #248
	str r0, [r12, #0]
	add r12, sp, #248
	str r1, [r12, #4]
	add r12, sp, #248
	str r2, [r12, #8]
	add r12, sp, #248
	str r3, [r12, #12]
	ldr lr, [sp, #280]
	add r12, sp, #248
	str lr, [r12, #16]
	ldr lr, [sp, #284]
	add r12, sp, #248
	str lr, [r12, #20]
	ldr r0, [sp, #264]
	lsl r0, r0, #8
	add r12, sp, #236
	str r0, [r12, #8]
	movw r0, #26963
	movt r0, #17767
	str r0, [r12, #0]
	movw r0, #13412
	movt r0, #14388
	str r0, [r12, #4]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	str r1, [r0, #8]
	str r1, [r0, #12]
	str r1, [r0, #16]
	str r1, [r0, #20]
	str r1, [r0, #24]
	str r1, [r0, #28]
	str r1, [r0, #32]
	str r1, [r0, #36]
	str r1, [r0, #40]
	str r1, [r0, #44]
	str r1, [r0, #48]
	str r1, [r0, #52]
	str r1, [r0, #56]
	str r1, [r0, #60]
	str r1, [r0, #64]
	str r1, [r0, #68]
	str r1, [r0, #72]
	str r1, [r0, #76]
	str r1, [r0, #80]
	str r1, [r0, #84]
	str r1, [r0, #88]
	str r1, [r0, #92]
	str r1, [r0, #96]
	str r1, [r0, #100]
	str r1, [r0, #104]
	str r1, [r0, #108]
	str r1, [r0, #112]
	str r1, [r0, #116]
	str r1, [r0, #120]
	str r1, [r0, #124]
	str r1, [r0, #128]
	str r1, [r0, #132]
	str r1, [r0, #136]
	str r1, [r0, #140]
	str r1, [r0, #144]
	str r1, [r0, #148]
	str r1, [r0, #152]
	str r1, [r0, #156]
	str r1, [r0, #160]
	str r1, [r0, #164]
	str r1, [r0, #168]
	str r1, [r0, #172]
	str r1, [r0, #176]
	str r1, [r0, #180]
	str r1, [r0, #184]
	str r1, [r0, #188]
	str r1, [r0, #192]
	str r1, [r0, #196]
	movw r0, #57
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	movw r2, #0
	ldr r3, [sp, #252]
	add r3, r3, #0
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	movw r3, #31
	bl {vg_keccak_pad_scratch}
	movw r0, #114
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	movw r2, #0
	add r3, sp, #122
	bl {vg_keccak_squeeze_scratch}
	add r12, sp, #122
	ldrb r0, [r12, #0]
	and r0, r0, #252
	strb r0, [r12, #0]
	ldrb r0, [r12, #55]
	orr r0, r0, #128
	strb r0, [r12, #55]
	movw r0, #0
	strb r0, [r12, #56]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	str r1, [r0, #8]
	str r1, [r0, #12]
	str r1, [r0, #16]
	str r1, [r0, #20]
	str r1, [r0, #24]
	str r1, [r0, #28]
	str r1, [r0, #32]
	str r1, [r0, #36]
	str r1, [r0, #40]
	str r1, [r0, #44]
	str r1, [r0, #48]
	str r1, [r0, #52]
	str r1, [r0, #56]
	str r1, [r0, #60]
	str r1, [r0, #64]
	str r1, [r0, #68]
	str r1, [r0, #72]
	str r1, [r0, #76]
	str r1, [r0, #80]
	str r1, [r0, #84]
	str r1, [r0, #88]
	str r1, [r0, #92]
	str r1, [r0, #96]
	str r1, [r0, #100]
	str r1, [r0, #104]
	str r1, [r0, #108]
	str r1, [r0, #112]
	str r1, [r0, #116]
	str r1, [r0, #120]
	str r1, [r0, #124]
	str r1, [r0, #128]
	str r1, [r0, #132]
	str r1, [r0, #136]
	str r1, [r0, #140]
	str r1, [r0, #144]
	str r1, [r0, #148]
	str r1, [r0, #152]
	str r1, [r0, #156]
	str r1, [r0, #160]
	str r1, [r0, #164]
	str r1, [r0, #168]
	str r1, [r0, #172]
	str r1, [r0, #176]
	str r1, [r0, #180]
	str r1, [r0, #184]
	str r1, [r0, #188]
	str r1, [r0, #192]
	str r1, [r0, #196]
	movw r0, #10
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	movw r2, #0
	add r3, sp, #236
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	ldr r0, [sp, #264]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	ldr r3, [sp, #260]
	add r3, r3, #0
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	movw r0, #57
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	add r3, sp, #179
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	ldr r0, [sp, #288]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	ldr r3, [sp, #268]
	add r3, r3, #0
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	movw r3, #31
	bl {vg_keccak_pad_scratch}
	movw r0, #114
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	movw r2, #0
	add r3, sp, #8
	bl {vg_keccak_squeeze_scratch}
	ldr r0, [sp, #248]
	add r0, r0, #57
	add r1, sp, #8
	ldr r2, [sp, #292]
	add r2, r2, #0
	bl {vg_ed448_scalar_reduce}
	ldr r0, [sp, #248]
	add r0, r0, #0
	ldr r1, [sp, #248]
	add r1, r1, #57
	ldr r2, [sp, #292]
	add r2, r2, #0
	bl {vg_ed448_scalar_base}
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	str r1, [r0, #8]
	str r1, [r0, #12]
	str r1, [r0, #16]
	str r1, [r0, #20]
	str r1, [r0, #24]
	str r1, [r0, #28]
	str r1, [r0, #32]
	str r1, [r0, #36]
	str r1, [r0, #40]
	str r1, [r0, #44]
	str r1, [r0, #48]
	str r1, [r0, #52]
	str r1, [r0, #56]
	str r1, [r0, #60]
	str r1, [r0, #64]
	str r1, [r0, #68]
	str r1, [r0, #72]
	str r1, [r0, #76]
	str r1, [r0, #80]
	str r1, [r0, #84]
	str r1, [r0, #88]
	str r1, [r0, #92]
	str r1, [r0, #96]
	str r1, [r0, #100]
	str r1, [r0, #104]
	str r1, [r0, #108]
	str r1, [r0, #112]
	str r1, [r0, #116]
	str r1, [r0, #120]
	str r1, [r0, #124]
	str r1, [r0, #128]
	str r1, [r0, #132]
	str r1, [r0, #136]
	str r1, [r0, #140]
	str r1, [r0, #144]
	str r1, [r0, #148]
	str r1, [r0, #152]
	str r1, [r0, #156]
	str r1, [r0, #160]
	str r1, [r0, #164]
	str r1, [r0, #168]
	str r1, [r0, #172]
	str r1, [r0, #176]
	str r1, [r0, #180]
	str r1, [r0, #184]
	str r1, [r0, #188]
	str r1, [r0, #192]
	str r1, [r0, #196]
	movw r0, #10
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	movw r2, #0
	add r3, sp, #236
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	ldr r0, [sp, #264]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	ldr r3, [sp, #260]
	add r3, r3, #0
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	movw r0, #57
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	ldr r3, [sp, #248]
	add r3, r3, #0
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	movw r0, #57
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	ldr r3, [sp, #256]
	add r3, r3, #0
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	ldr r0, [sp, #288]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	ldr r3, [sp, #268]
	add r3, r3, #0
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	movw r3, #31
	bl {vg_keccak_pad_scratch}
	movw r0, #114
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #292]
	add r0, r0, #0
	movw r1, #136
	movw r2, #0
	add r3, sp, #8
	bl {vg_keccak_squeeze_scratch}
	add r0, sp, #179
	add r1, sp, #8
	ldr r2, [sp, #292]
	add r2, r2, #0
	bl {vg_ed448_scalar_reduce}
	ldr r0, [sp, #292]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #248]
	add r0, r0, #57
	ldr r1, [sp, #248]
	add r1, r1, #57
	add r2, sp, #179
	add r3, sp, #122
	bl {vg_ed448_scalar_mul_add}
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #8]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #12]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #16]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #20]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #24]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #28]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #32]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #36]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #40]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #44]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #48]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #52]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #56]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #60]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #64]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #68]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #72]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #76]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #80]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #84]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #88]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #96]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #100]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #104]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #108]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #112]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #116]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #120]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #128]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #132]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #136]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #140]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #144]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #148]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #152]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #156]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #160]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #164]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #168]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #172]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #176]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #180]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #184]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #188]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #192]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #196]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #200]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #204]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #208]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #212]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #216]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #220]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #224]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #228]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #232]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #236]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #240]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #244]
	add sp, sp, #248
	add sp, sp, #24
	ldr r12, [sp], #4
	ldr lr, [sp], #4
	bx lr

vg_ed448_verify:
	lsr r12, r2, #8
	cmp r12, #0
	beq 20f
	movw r0, #0
	b 21f
20:
	push {lr}
	push {r12}
	sub sp, sp, #24
	sub sp, sp, #248
	add r12, sp, #248
	str r0, [r12, #0]
	add r12, sp, #248
	str r1, [r12, #4]
	add r12, sp, #248
	str r2, [r12, #8]
	add r12, sp, #248
	str r3, [r12, #12]
	ldr lr, [sp, #280]
	add r12, sp, #248
	str lr, [r12, #16]
	ldr lr, [sp, #284]
	add r12, sp, #248
	str lr, [r12, #20]
	ldr r0, [sp, #256]
	lsl r0, r0, #8
	add r12, sp, #24
	str r0, [r12, #8]
	movw r0, #26963
	movt r0, #17767
	str r0, [r12, #0]
	movw r0, #13412
	movt r0, #14388
	str r0, [r12, #4]
	ldr r0, [sp, #288]
	add r0, r0, #0
	movw r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	str r1, [r0, #8]
	str r1, [r0, #12]
	str r1, [r0, #16]
	str r1, [r0, #20]
	str r1, [r0, #24]
	str r1, [r0, #28]
	str r1, [r0, #32]
	str r1, [r0, #36]
	str r1, [r0, #40]
	str r1, [r0, #44]
	str r1, [r0, #48]
	str r1, [r0, #52]
	str r1, [r0, #56]
	str r1, [r0, #60]
	str r1, [r0, #64]
	str r1, [r0, #68]
	str r1, [r0, #72]
	str r1, [r0, #76]
	str r1, [r0, #80]
	str r1, [r0, #84]
	str r1, [r0, #88]
	str r1, [r0, #92]
	str r1, [r0, #96]
	str r1, [r0, #100]
	str r1, [r0, #104]
	str r1, [r0, #108]
	str r1, [r0, #112]
	str r1, [r0, #116]
	str r1, [r0, #120]
	str r1, [r0, #124]
	str r1, [r0, #128]
	str r1, [r0, #132]
	str r1, [r0, #136]
	str r1, [r0, #140]
	str r1, [r0, #144]
	str r1, [r0, #148]
	str r1, [r0, #152]
	str r1, [r0, #156]
	str r1, [r0, #160]
	str r1, [r0, #164]
	str r1, [r0, #168]
	str r1, [r0, #172]
	str r1, [r0, #176]
	str r1, [r0, #180]
	str r1, [r0, #184]
	str r1, [r0, #188]
	str r1, [r0, #192]
	str r1, [r0, #196]
	movw r0, #10
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #288]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #288]
	add r0, r0, #0
	movw r1, #136
	movw r2, #0
	add r3, sp, #24
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	ldr r0, [sp, #256]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #288]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #288]
	add r0, r0, #0
	movw r1, #136
	ldr r3, [sp, #252]
	add r3, r3, #0
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	movw r0, #57
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #288]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #288]
	add r0, r0, #0
	movw r1, #136
	ldr r3, [sp, #268]
	add r3, r3, #0
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	movw r0, #57
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #288]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #288]
	add r0, r0, #0
	movw r1, #136
	ldr r3, [sp, #248]
	add r3, r3, #0
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	ldr r0, [sp, #264]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #288]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #288]
	add r0, r0, #0
	movw r1, #136
	ldr r3, [sp, #260]
	add r3, r3, #0
	bl {vg_keccak_absorb_scratch}
	mov r2, r0
	ldr r0, [sp, #288]
	add r0, r0, #208
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #288]
	add r0, r0, #0
	movw r1, #136
	movw r3, #31
	bl {vg_keccak_pad_scratch}
	movw r0, #114
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #288]
	add r0, r0, #208
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #288]
	add r0, r0, #0
	movw r1, #136
	movw r2, #0
	add r3, sp, #40
	bl {vg_keccak_squeeze_scratch}
	add r0, sp, #160
	add r1, sp, #40
	ldr r2, [sp, #288]
	add r2, r2, #0
	bl {vg_ed448_scalar_reduce}
	ldr r0, [sp, #248]
	add r0, r0, #0
	ldr r1, [sp, #268]
	add r1, r1, #0
	add r2, sp, #160
	ldr r3, [sp, #288]
	add r3, r3, #0
	bl {vg_ed448_verify_equation}
	add sp, sp, #248
	add sp, sp, #24
	ldr r12, [sp], #4
	ldr lr, [sp], #4
21:
	bx lr
