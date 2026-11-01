// The functions of `src/ed25519.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_public_key:
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
	bl {vg_sha512_init}
	ldr r0, [sp, #252]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	movw r0, #32
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #256]
	add r0, r0, #192
	add r12, sp, #8
	str r0, [r12, #0]
	ldr r0, [sp, #256]
	add r0, r0, #0
	movw r2, #0
	movw r3, #0
	bl {vg_sha512_update_scratch}
	add r0, sp, #184
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #256]
	add r0, r0, #192
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #256]
	add r0, r0, #0
	movw r2, #32
	movw r3, #0
	bl {vg_sha512_finalize_scratch}
	ldr r0, [sp, #184]
	movw r1, #65528
	movt r1, #65535
	and r0, r0, r1
	add r12, sp, #24
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	add r12, sp, #24
	str r0, [r12, #4]
	ldr r0, [sp, #192]
	add r12, sp, #24
	str r0, [r12, #8]
	ldr r0, [sp, #196]
	add r12, sp, #24
	str r0, [r12, #12]
	ldr r0, [sp, #200]
	add r12, sp, #24
	str r0, [r12, #16]
	ldr r0, [sp, #204]
	add r12, sp, #24
	str r0, [r12, #20]
	ldr r0, [sp, #208]
	add r12, sp, #24
	str r0, [r12, #24]
	ldr r0, [sp, #212]
	movw r1, #65535
	movt r1, #16383
	and r0, r0, r1
	movw r1, #0
	movt r1, #16384
	orr r0, r0, r1
	add r12, sp, #24
	str r0, [r12, #28]
	ldr r0, [sp, #248]
	add r0, r0, #0
	add r1, sp, #24
	ldr r2, [sp, #256]
	add r2, r2, #0
	bl {vg_ed25519_scalar_base}
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

vg_ed25519_sign_cached:
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
	ldr r0, [sp, #268]
	add r0, r0, #0
	bl {vg_sha512_init}
	ldr r0, [sp, #252]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	movw r0, #32
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #192
	add r12, sp, #8
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #0
	movw r2, #0
	movw r3, #0
	bl {vg_sha512_update_scratch}
	add r0, sp, #184
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #192
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #0
	movw r2, #32
	movw r3, #0
	bl {vg_sha512_finalize_scratch}
	ldr r0, [sp, #184]
	movw r1, #65528
	movt r1, #65535
	and r0, r0, r1
	add r12, sp, #24
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	add r12, sp, #24
	str r0, [r12, #4]
	ldr r0, [sp, #192]
	add r12, sp, #24
	str r0, [r12, #8]
	ldr r0, [sp, #196]
	add r12, sp, #24
	str r0, [r12, #12]
	ldr r0, [sp, #200]
	add r12, sp, #24
	str r0, [r12, #16]
	ldr r0, [sp, #204]
	add r12, sp, #24
	str r0, [r12, #20]
	ldr r0, [sp, #208]
	add r12, sp, #24
	str r0, [r12, #24]
	ldr r0, [sp, #212]
	movw r1, #65535
	movt r1, #16383
	and r0, r0, r1
	movw r1, #0
	movt r1, #16384
	orr r0, r0, r1
	add r12, sp, #24
	str r0, [r12, #28]
	ldr r0, [sp, #216]
	add r12, sp, #0
	str r0, [r12, #56]
	ldr r0, [sp, #220]
	add r12, sp, #0
	str r0, [r12, #60]
	ldr r0, [sp, #224]
	add r12, sp, #0
	str r0, [r12, #64]
	ldr r0, [sp, #228]
	add r12, sp, #0
	str r0, [r12, #68]
	ldr r0, [sp, #232]
	add r12, sp, #0
	str r0, [r12, #72]
	ldr r0, [sp, #236]
	add r12, sp, #0
	str r0, [r12, #76]
	ldr r0, [sp, #240]
	add r12, sp, #0
	str r0, [r12, #80]
	ldr r0, [sp, #244]
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #268]
	add r0, r0, #0
	bl {vg_sha512_init}
	add r0, sp, #56
	add r12, sp, #0
	str r0, [r12, #0]
	movw r0, #32
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #192
	add r12, sp, #8
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #0
	movw r2, #0
	movw r3, #0
	bl {vg_sha512_update_scratch}
	ldr r0, [sp, #260]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #264]
	add r0, r0, #0
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #192
	add r12, sp, #8
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #0
	movw r2, #32
	movw r3, #0
	bl {vg_sha512_update_scratch}
	add r0, sp, #184
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #192
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #0
	ldr r2, [sp, #264]
	add r2, r2, #32
	movw r3, #0
	bl {vg_sha512_finalize_scratch}
	add r0, sp, #88
	add r1, sp, #184
	ldr r2, [sp, #268]
	add r2, r2, #0
	bl {vg_ed25519_scalar_reduce}
	ldr r0, [sp, #248]
	add r0, r0, #0
	add r1, sp, #88
	ldr r2, [sp, #268]
	add r2, r2, #0
	bl {vg_ed25519_scalar_base}
	ldr r0, [sp, #268]
	add r0, r0, #0
	bl {vg_sha512_init}
	ldr r0, [sp, #248]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	movw r0, #32
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #192
	add r12, sp, #8
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #0
	movw r2, #0
	movw r3, #0
	bl {vg_sha512_update_scratch}
	ldr r0, [sp, #256]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	movw r0, #32
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #192
	add r12, sp, #8
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #0
	movw r2, #32
	movw r3, #0
	bl {vg_sha512_update_scratch}
	ldr r0, [sp, #260]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #264]
	add r0, r0, #0
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #192
	add r12, sp, #8
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #0
	movw r2, #64
	movw r3, #0
	bl {vg_sha512_update_scratch}
	add r0, sp, #184
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #192
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #268]
	add r0, r0, #0
	ldr r2, [sp, #264]
	add r2, r2, #64
	movw r3, #0
	bl {vg_sha512_finalize_scratch}
	add r0, sp, #120
	add r1, sp, #184
	ldr r2, [sp, #268]
	add r2, r2, #0
	bl {vg_ed25519_scalar_reduce}
	ldr r0, [sp, #268]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #248]
	add r0, r0, #32
	add r1, sp, #88
	add r2, sp, #120
	add r3, sp, #24
	bl {vg_ed25519_scalar_mul_add}
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

vg_ed25519_verify:
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
	ldr r0, [sp, #264]
	add r0, r0, #0
	bl {vg_sha512_init}
	ldr r0, [sp, #260]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	movw r0, #32
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #264]
	add r0, r0, #192
	add r12, sp, #8
	str r0, [r12, #0]
	ldr r0, [sp, #264]
	add r0, r0, #0
	movw r2, #0
	movw r3, #0
	bl {vg_sha512_update_scratch}
	ldr r0, [sp, #248]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	movw r0, #32
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #264]
	add r0, r0, #192
	add r12, sp, #8
	str r0, [r12, #0]
	ldr r0, [sp, #264]
	add r0, r0, #0
	movw r2, #32
	movw r3, #0
	bl {vg_sha512_update_scratch}
	ldr r0, [sp, #252]
	add r0, r0, #0
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #256]
	add r0, r0, #0
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #264]
	add r0, r0, #192
	add r12, sp, #8
	str r0, [r12, #0]
	ldr r0, [sp, #264]
	add r0, r0, #0
	movw r2, #64
	movw r3, #0
	bl {vg_sha512_update_scratch}
	add r0, sp, #184
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [sp, #264]
	add r0, r0, #192
	add r12, sp, #4
	str r0, [r12, #0]
	ldr r0, [sp, #264]
	add r0, r0, #0
	ldr r2, [sp, #256]
	add r2, r2, #64
	movw r3, #0
	bl {vg_sha512_finalize_scratch}
	add r0, sp, #120
	add r1, sp, #184
	ldr r2, [sp, #264]
	add r2, r2, #0
	bl {vg_ed25519_scalar_reduce}
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
	ldr r0, [sp, #248]
	add r0, r0, #0
	ldr r1, [sp, #260]
	add r1, r1, #0
	add r2, sp, #120
	ldr r3, [sp, #264]
	add r3, r3, #0
	bl {vg_ed25519_verify_equation}
	add sp, sp, #248
	add sp, sp, #24
	ldr r12, [sp], #4
	ldr lr, [sp], #4
	bx lr
