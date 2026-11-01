// The functions of `src/p224_mont.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p224_mul_mod_p:
	mov r12, r0
	str r4, [r12, #4040]
	str r5, [r12, #4044]
	str r6, [r12, #4048]
	str r7, [r12, #4052]
	str r8, [r12, #4056]
	str r9, [r12, #4060]
	str lr, [r12, #4064]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #4008]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4012]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4016]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4020]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4024]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4028]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4032]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4036]
	add lr, r12, r1
	add r1, r12, r2
	add r4, r12, r3
	mov r7, #0
	str r7, [r12, #3840]
	str r7, [r12, #3844]
	str r7, [r12, #3848]
	str r7, [r12, #3852]
	str r7, [r12, #3856]
	str r7, [r12, #3860]
	str r7, [r12, #3864]
	str r7, [r12, #3868]
	str r7, [r12, #3872]
	str r7, [r12, #3876]
	str r7, [r12, #3880]
	str r7, [r12, #3884]
	str r7, [r12, #3888]
	str r7, [r12, #3892]
	str r7, [r12, #3896]
	str r7, [r12, #3900]
	str r7, [r12, #3904]
	str r7, [r12, #3908]
	str r7, [r12, #3912]
	str r7, [r12, #3916]
	str r7, [r12, #3920]
	str r7, [r12, #3924]
	str r7, [r12, #3928]
	str r7, [r12, #3932]
	str r7, [r12, #3936]
	str r7, [r12, #3940]
	str r7, [r12, #3944]
	str r7, [r12, #3948]
	str r7, [r12, #3952]
	str r7, [r12, #3956]
	str r7, [r12, #3960]
	str r7, [r12, #3964]
	str r7, [r12, #3968]
	str r7, [r12, #3972]
	movw r6, #65535
	mov r0, r12
	mov r1, r1
	mov r9, #8
20:
	ldr r8, [r1, #0]
	and r2, r8, r6
	mov r3, #0
	ldr r7, [r4, #0]
	and r7, r7, r6
	ldr r5, [r0, #3840]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3840]
	lsr r3, r5, #16
	ldr r7, [r4, #0]
	lsr r7, r7, #16
	ldr r5, [r0, #3844]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3844]
	lsr r3, r5, #16
	ldr r7, [r4, #4]
	and r7, r7, r6
	ldr r5, [r0, #3848]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3848]
	lsr r3, r5, #16
	ldr r7, [r4, #4]
	lsr r7, r7, #16
	ldr r5, [r0, #3852]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3852]
	lsr r3, r5, #16
	ldr r7, [r4, #8]
	and r7, r7, r6
	ldr r5, [r0, #3856]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3856]
	lsr r3, r5, #16
	ldr r7, [r4, #8]
	lsr r7, r7, #16
	ldr r5, [r0, #3860]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3860]
	lsr r3, r5, #16
	ldr r7, [r4, #12]
	and r7, r7, r6
	ldr r5, [r0, #3864]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3864]
	lsr r3, r5, #16
	ldr r7, [r4, #12]
	lsr r7, r7, #16
	ldr r5, [r0, #3868]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3868]
	lsr r3, r5, #16
	ldr r7, [r4, #16]
	and r7, r7, r6
	ldr r5, [r0, #3872]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3872]
	lsr r3, r5, #16
	ldr r7, [r4, #16]
	lsr r7, r7, #16
	ldr r5, [r0, #3876]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3876]
	lsr r3, r5, #16
	ldr r7, [r4, #20]
	and r7, r7, r6
	ldr r5, [r0, #3880]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3880]
	lsr r3, r5, #16
	ldr r7, [r4, #20]
	lsr r7, r7, #16
	ldr r5, [r0, #3884]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3884]
	lsr r3, r5, #16
	ldr r7, [r4, #24]
	and r7, r7, r6
	ldr r5, [r0, #3888]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3888]
	lsr r3, r5, #16
	ldr r7, [r4, #24]
	lsr r7, r7, #16
	ldr r5, [r0, #3892]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3892]
	lsr r3, r5, #16
	ldr r7, [r4, #28]
	and r7, r7, r6
	ldr r5, [r0, #3896]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3896]
	lsr r3, r5, #16
	ldr r7, [r4, #28]
	lsr r7, r7, #16
	ldr r5, [r0, #3900]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3900]
	lsr r3, r5, #16
	ldr r5, [r0, #3904]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3904]
	ldr r7, [r0, #3908]
	add r7, r7, r5, lsr #16
	str r7, [r0, #3908]
	ldr r2, [r0, #3840]
	movw r7, #65535
	mul r2, r2, r7
	and r2, r2, r6
	mov r3, #0
	ldr r7, [r12, #4008]
	and r7, r7, r6
	ldr r5, [r0, #3840]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3840]
	lsr r3, r5, #16
	ldr r7, [r12, #4008]
	lsr r7, r7, #16
	ldr r5, [r0, #3844]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3844]
	lsr r3, r5, #16
	ldr r7, [r12, #4012]
	and r7, r7, r6
	ldr r5, [r0, #3848]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3848]
	lsr r3, r5, #16
	ldr r7, [r12, #4012]
	lsr r7, r7, #16
	ldr r5, [r0, #3852]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3852]
	lsr r3, r5, #16
	ldr r7, [r12, #4016]
	and r7, r7, r6
	ldr r5, [r0, #3856]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3856]
	lsr r3, r5, #16
	ldr r7, [r12, #4016]
	lsr r7, r7, #16
	ldr r5, [r0, #3860]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3860]
	lsr r3, r5, #16
	ldr r7, [r12, #4020]
	and r7, r7, r6
	ldr r5, [r0, #3864]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3864]
	lsr r3, r5, #16
	ldr r7, [r12, #4020]
	lsr r7, r7, #16
	ldr r5, [r0, #3868]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3868]
	lsr r3, r5, #16
	ldr r7, [r12, #4024]
	and r7, r7, r6
	ldr r5, [r0, #3872]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3872]
	lsr r3, r5, #16
	ldr r7, [r12, #4024]
	lsr r7, r7, #16
	ldr r5, [r0, #3876]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3876]
	lsr r3, r5, #16
	ldr r7, [r12, #4028]
	and r7, r7, r6
	ldr r5, [r0, #3880]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3880]
	lsr r3, r5, #16
	ldr r7, [r12, #4028]
	lsr r7, r7, #16
	ldr r5, [r0, #3884]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3884]
	lsr r3, r5, #16
	ldr r7, [r12, #4032]
	and r7, r7, r6
	ldr r5, [r0, #3888]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3888]
	lsr r3, r5, #16
	ldr r7, [r12, #4032]
	lsr r7, r7, #16
	ldr r5, [r0, #3892]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3892]
	lsr r3, r5, #16
	ldr r7, [r12, #4036]
	and r7, r7, r6
	ldr r5, [r0, #3896]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3896]
	lsr r3, r5, #16
	ldr r7, [r12, #4036]
	lsr r7, r7, #16
	ldr r5, [r0, #3900]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3900]
	lsr r3, r5, #16
	ldr r5, [r0, #3904]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3904]
	ldr r7, [r0, #3908]
	add r7, r7, r5, lsr #16
	str r7, [r0, #3908]
	add r0, r0, #4
	lsr r2, r8, #16
	mov r3, #0
	ldr r7, [r4, #0]
	and r7, r7, r6
	ldr r5, [r0, #3840]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3840]
	lsr r3, r5, #16
	ldr r7, [r4, #0]
	lsr r7, r7, #16
	ldr r5, [r0, #3844]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3844]
	lsr r3, r5, #16
	ldr r7, [r4, #4]
	and r7, r7, r6
	ldr r5, [r0, #3848]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3848]
	lsr r3, r5, #16
	ldr r7, [r4, #4]
	lsr r7, r7, #16
	ldr r5, [r0, #3852]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3852]
	lsr r3, r5, #16
	ldr r7, [r4, #8]
	and r7, r7, r6
	ldr r5, [r0, #3856]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3856]
	lsr r3, r5, #16
	ldr r7, [r4, #8]
	lsr r7, r7, #16
	ldr r5, [r0, #3860]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3860]
	lsr r3, r5, #16
	ldr r7, [r4, #12]
	and r7, r7, r6
	ldr r5, [r0, #3864]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3864]
	lsr r3, r5, #16
	ldr r7, [r4, #12]
	lsr r7, r7, #16
	ldr r5, [r0, #3868]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3868]
	lsr r3, r5, #16
	ldr r7, [r4, #16]
	and r7, r7, r6
	ldr r5, [r0, #3872]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3872]
	lsr r3, r5, #16
	ldr r7, [r4, #16]
	lsr r7, r7, #16
	ldr r5, [r0, #3876]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3876]
	lsr r3, r5, #16
	ldr r7, [r4, #20]
	and r7, r7, r6
	ldr r5, [r0, #3880]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3880]
	lsr r3, r5, #16
	ldr r7, [r4, #20]
	lsr r7, r7, #16
	ldr r5, [r0, #3884]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3884]
	lsr r3, r5, #16
	ldr r7, [r4, #24]
	and r7, r7, r6
	ldr r5, [r0, #3888]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3888]
	lsr r3, r5, #16
	ldr r7, [r4, #24]
	lsr r7, r7, #16
	ldr r5, [r0, #3892]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3892]
	lsr r3, r5, #16
	ldr r7, [r4, #28]
	and r7, r7, r6
	ldr r5, [r0, #3896]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3896]
	lsr r3, r5, #16
	ldr r7, [r4, #28]
	lsr r7, r7, #16
	ldr r5, [r0, #3900]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3900]
	lsr r3, r5, #16
	ldr r5, [r0, #3904]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3904]
	ldr r7, [r0, #3908]
	add r7, r7, r5, lsr #16
	str r7, [r0, #3908]
	ldr r2, [r0, #3840]
	movw r7, #65535
	mul r2, r2, r7
	and r2, r2, r6
	mov r3, #0
	ldr r7, [r12, #4008]
	and r7, r7, r6
	ldr r5, [r0, #3840]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3840]
	lsr r3, r5, #16
	ldr r7, [r12, #4008]
	lsr r7, r7, #16
	ldr r5, [r0, #3844]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3844]
	lsr r3, r5, #16
	ldr r7, [r12, #4012]
	and r7, r7, r6
	ldr r5, [r0, #3848]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3848]
	lsr r3, r5, #16
	ldr r7, [r12, #4012]
	lsr r7, r7, #16
	ldr r5, [r0, #3852]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3852]
	lsr r3, r5, #16
	ldr r7, [r12, #4016]
	and r7, r7, r6
	ldr r5, [r0, #3856]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3856]
	lsr r3, r5, #16
	ldr r7, [r12, #4016]
	lsr r7, r7, #16
	ldr r5, [r0, #3860]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3860]
	lsr r3, r5, #16
	ldr r7, [r12, #4020]
	and r7, r7, r6
	ldr r5, [r0, #3864]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3864]
	lsr r3, r5, #16
	ldr r7, [r12, #4020]
	lsr r7, r7, #16
	ldr r5, [r0, #3868]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3868]
	lsr r3, r5, #16
	ldr r7, [r12, #4024]
	and r7, r7, r6
	ldr r5, [r0, #3872]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3872]
	lsr r3, r5, #16
	ldr r7, [r12, #4024]
	lsr r7, r7, #16
	ldr r5, [r0, #3876]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3876]
	lsr r3, r5, #16
	ldr r7, [r12, #4028]
	and r7, r7, r6
	ldr r5, [r0, #3880]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3880]
	lsr r3, r5, #16
	ldr r7, [r12, #4028]
	lsr r7, r7, #16
	ldr r5, [r0, #3884]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3884]
	lsr r3, r5, #16
	ldr r7, [r12, #4032]
	and r7, r7, r6
	ldr r5, [r0, #3888]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3888]
	lsr r3, r5, #16
	ldr r7, [r12, #4032]
	lsr r7, r7, #16
	ldr r5, [r0, #3892]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3892]
	lsr r3, r5, #16
	ldr r7, [r12, #4036]
	and r7, r7, r6
	ldr r5, [r0, #3896]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3896]
	lsr r3, r5, #16
	ldr r7, [r12, #4036]
	lsr r7, r7, #16
	ldr r5, [r0, #3900]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3900]
	lsr r3, r5, #16
	ldr r5, [r0, #3904]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3904]
	ldr r7, [r0, #3908]
	add r7, r7, r5, lsr #16
	str r7, [r0, #3908]
	add r0, r0, #4
	add r1, r1, #4
	subs r9, r9, #1
	bne 20b
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #4008]
	ldr r5, [r12, #3904]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3908]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3976]
	ldr r7, [r12, #4012]
	ldr r5, [r12, #3912]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3916]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3980]
	ldr r7, [r12, #4016]
	ldr r5, [r12, #3920]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3924]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3984]
	ldr r7, [r12, #4020]
	ldr r5, [r12, #3928]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3932]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3988]
	ldr r7, [r12, #4024]
	ldr r5, [r12, #3936]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3940]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3992]
	ldr r7, [r12, #4028]
	ldr r5, [r12, #3944]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3948]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3996]
	ldr r7, [r12, #4032]
	ldr r5, [r12, #3952]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3956]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4000]
	ldr r7, [r12, #4036]
	ldr r5, [r12, #3960]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3964]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4004]
	ldr r5, [r12, #3968]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3904]
	ldr r7, [r12, #3908]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3976]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3912]
	ldr r7, [r12, #3916]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3980]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3920]
	ldr r7, [r12, #3924]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3984]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3928]
	ldr r7, [r12, #3932]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3988]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3936]
	ldr r7, [r12, #3940]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3992]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3944]
	ldr r7, [r12, #3948]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3996]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r5, [r12, #3952]
	ldr r7, [r12, #3956]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4000]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #24]
	ldr r5, [r12, #3960]
	ldr r7, [r12, #3964]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4004]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #28]
	ldr r4, [r12, #4040]
	ldr r5, [r12, #4044]
	ldr r6, [r12, #4048]
	ldr r7, [r12, #4052]
	ldr r8, [r12, #4056]
	ldr r9, [r12, #4060]
	ldr lr, [r12, #4064]
	bx lr

vg_p224_mul_mod_p_umaal:
	mov r12, r0
	str r4, [r12, #4040]
	str r5, [r12, #4044]
	str r6, [r12, #4048]
	str r7, [r12, #4052]
	str r8, [r12, #4056]
	str r9, [r12, #4060]
	str lr, [r12, #4064]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #4008]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4012]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4016]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4020]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4024]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4028]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4032]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4036]
	add lr, r12, r1
	add r1, r12, r2
	add r4, r12, r3
	mov r7, #0
	str r7, [r12, #3840]
	str r7, [r12, #3844]
	str r7, [r12, #3848]
	str r7, [r12, #3852]
	str r7, [r12, #3856]
	str r7, [r12, #3860]
	str r7, [r12, #3864]
	str r7, [r12, #3868]
	str r7, [r12, #3872]
	str r7, [r12, #3876]
	mov r9, #8
20:
	ldr r2, [r1, #0]
	mov r3, #0
	ldr r7, [r4, #0]
	ldr r5, [r12, #3840]
	umaal r5, r3, r2, r7
	str r5, [r12, #3840]
	ldr r7, [r4, #4]
	ldr r5, [r12, #3844]
	umaal r5, r3, r2, r7
	str r5, [r12, #3844]
	ldr r7, [r4, #8]
	ldr r5, [r12, #3848]
	umaal r5, r3, r2, r7
	str r5, [r12, #3848]
	ldr r7, [r4, #12]
	ldr r5, [r12, #3852]
	umaal r5, r3, r2, r7
	str r5, [r12, #3852]
	ldr r7, [r4, #16]
	ldr r5, [r12, #3856]
	umaal r5, r3, r2, r7
	str r5, [r12, #3856]
	ldr r7, [r4, #20]
	ldr r5, [r12, #3860]
	umaal r5, r3, r2, r7
	str r5, [r12, #3860]
	ldr r7, [r4, #24]
	ldr r5, [r12, #3864]
	umaal r5, r3, r2, r7
	str r5, [r12, #3864]
	ldr r7, [r4, #28]
	ldr r5, [r12, #3868]
	umaal r5, r3, r2, r7
	str r5, [r12, #3868]
	ldr r5, [r12, #3872]
	ldr r6, [r12, #3876]
	adds r5, r5, r3
	adc r6, r6, #0
	str r5, [r12, #3872]
	str r6, [r12, #3876]
	ldr r2, [r12, #3840]
	movw r7, #65535
	movt r7, #65535
	mul r2, r2, r7
	mov r3, #0
	ldr r7, [r12, #4008]
	ldr r5, [r12, #3840]
	umaal r5, r3, r2, r7
	str r5, [r12, #3840]
	ldr r7, [r12, #4012]
	ldr r5, [r12, #3844]
	umaal r5, r3, r2, r7
	str r5, [r12, #3844]
	ldr r7, [r12, #4016]
	ldr r5, [r12, #3848]
	umaal r5, r3, r2, r7
	str r5, [r12, #3848]
	ldr r7, [r12, #4020]
	ldr r5, [r12, #3852]
	umaal r5, r3, r2, r7
	str r5, [r12, #3852]
	ldr r7, [r12, #4024]
	ldr r5, [r12, #3856]
	umaal r5, r3, r2, r7
	str r5, [r12, #3856]
	ldr r7, [r12, #4028]
	ldr r5, [r12, #3860]
	umaal r5, r3, r2, r7
	str r5, [r12, #3860]
	ldr r7, [r12, #4032]
	ldr r5, [r12, #3864]
	umaal r5, r3, r2, r7
	str r5, [r12, #3864]
	ldr r7, [r12, #4036]
	ldr r5, [r12, #3868]
	umaal r5, r3, r2, r7
	str r5, [r12, #3868]
	ldr r5, [r12, #3872]
	ldr r6, [r12, #3876]
	adds r5, r5, r3
	adc r6, r6, #0
	str r5, [r12, #3872]
	str r6, [r12, #3876]
	ldr r5, [r12, #3844]
	str r5, [r12, #3840]
	ldr r5, [r12, #3848]
	str r5, [r12, #3844]
	ldr r5, [r12, #3852]
	str r5, [r12, #3848]
	ldr r5, [r12, #3856]
	str r5, [r12, #3852]
	ldr r5, [r12, #3860]
	str r5, [r12, #3856]
	ldr r5, [r12, #3864]
	str r5, [r12, #3860]
	ldr r5, [r12, #3868]
	str r5, [r12, #3864]
	ldr r5, [r12, #3872]
	str r5, [r12, #3868]
	ldr r5, [r12, #3876]
	str r5, [r12, #3872]
	mov r5, #0
	str r5, [r12, #3876]
	add r1, r1, #4
	subs r9, r9, #1
	bne 20b
	movw r6, #65535
	ldr r7, [r12, #3840]
	and r7, r7, r6
	str r7, [r12, #3880]
	ldr r7, [r12, #3840]
	lsr r7, r7, #16
	str r7, [r12, #3884]
	ldr r7, [r12, #3844]
	and r7, r7, r6
	str r7, [r12, #3888]
	ldr r7, [r12, #3844]
	lsr r7, r7, #16
	str r7, [r12, #3892]
	ldr r7, [r12, #3848]
	and r7, r7, r6
	str r7, [r12, #3896]
	ldr r7, [r12, #3848]
	lsr r7, r7, #16
	str r7, [r12, #3900]
	ldr r7, [r12, #3852]
	and r7, r7, r6
	str r7, [r12, #3904]
	ldr r7, [r12, #3852]
	lsr r7, r7, #16
	str r7, [r12, #3908]
	ldr r7, [r12, #3856]
	and r7, r7, r6
	str r7, [r12, #3912]
	ldr r7, [r12, #3856]
	lsr r7, r7, #16
	str r7, [r12, #3916]
	ldr r7, [r12, #3860]
	and r7, r7, r6
	str r7, [r12, #3920]
	ldr r7, [r12, #3860]
	lsr r7, r7, #16
	str r7, [r12, #3924]
	ldr r7, [r12, #3864]
	and r7, r7, r6
	str r7, [r12, #3928]
	ldr r7, [r12, #3864]
	lsr r7, r7, #16
	str r7, [r12, #3932]
	ldr r7, [r12, #3868]
	and r7, r7, r6
	str r7, [r12, #3936]
	ldr r7, [r12, #3868]
	lsr r7, r7, #16
	str r7, [r12, #3940]
	ldr r7, [r12, #3872]
	and r7, r7, r6
	str r7, [r12, #3944]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #4008]
	ldr r5, [r12, #3880]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3884]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3976]
	ldr r7, [r12, #4012]
	ldr r5, [r12, #3888]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3892]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3980]
	ldr r7, [r12, #4016]
	ldr r5, [r12, #3896]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3900]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3984]
	ldr r7, [r12, #4020]
	ldr r5, [r12, #3904]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3908]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3988]
	ldr r7, [r12, #4024]
	ldr r5, [r12, #3912]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3916]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3992]
	ldr r7, [r12, #4028]
	ldr r5, [r12, #3920]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3924]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3996]
	ldr r7, [r12, #4032]
	ldr r5, [r12, #3928]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3932]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4000]
	ldr r7, [r12, #4036]
	ldr r5, [r12, #3936]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3940]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4004]
	ldr r5, [r12, #3944]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3880]
	ldr r7, [r12, #3884]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3976]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3888]
	ldr r7, [r12, #3892]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3980]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3896]
	ldr r7, [r12, #3900]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3984]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3904]
	ldr r7, [r12, #3908]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3988]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3912]
	ldr r7, [r12, #3916]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3992]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3920]
	ldr r7, [r12, #3924]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3996]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r5, [r12, #3928]
	ldr r7, [r12, #3932]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4000]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #24]
	ldr r5, [r12, #3936]
	ldr r7, [r12, #3940]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4004]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #28]
	ldr r4, [r12, #4040]
	ldr r5, [r12, #4044]
	ldr r6, [r12, #4048]
	ldr r7, [r12, #4052]
	ldr r8, [r12, #4056]
	ldr r9, [r12, #4060]
	ldr lr, [r12, #4064]
	bx lr

vg_p224_add_mod_p:
	mov r12, r0
	str r4, [r12, #4040]
	str r5, [r12, #4044]
	str r6, [r12, #4048]
	str r7, [r12, #4052]
	str r8, [r12, #4056]
	str r9, [r12, #4060]
	str lr, [r12, #4064]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #4008]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4012]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4016]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4020]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4024]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4028]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4032]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4036]
	add lr, r12, r1
	add r1, r12, r2
	add r2, r12, r3
	movw r6, #65535
	mov r3, #0
	ldr r7, [r1, #0]
	ldr r8, [r2, #0]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3840]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3844]
	lsr r3, r4, #16
	ldr r7, [r1, #4]
	ldr r8, [r2, #4]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3848]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3852]
	lsr r3, r4, #16
	ldr r7, [r1, #8]
	ldr r8, [r2, #8]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3856]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3860]
	lsr r3, r4, #16
	ldr r7, [r1, #12]
	ldr r8, [r2, #12]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3864]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3868]
	lsr r3, r4, #16
	ldr r7, [r1, #16]
	ldr r8, [r2, #16]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3872]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3876]
	lsr r3, r4, #16
	ldr r7, [r1, #20]
	ldr r8, [r2, #20]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3880]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3884]
	lsr r3, r4, #16
	ldr r7, [r1, #24]
	ldr r8, [r2, #24]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3888]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3892]
	lsr r3, r4, #16
	ldr r7, [r1, #28]
	ldr r8, [r2, #28]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3896]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3900]
	lsr r3, r4, #16
	str r3, [r12, #3904]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #4008]
	ldr r5, [r12, #3840]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3844]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3976]
	ldr r7, [r12, #4012]
	ldr r5, [r12, #3848]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3852]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3980]
	ldr r7, [r12, #4016]
	ldr r5, [r12, #3856]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3860]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3984]
	ldr r7, [r12, #4020]
	ldr r5, [r12, #3864]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3868]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3988]
	ldr r7, [r12, #4024]
	ldr r5, [r12, #3872]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3876]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3992]
	ldr r7, [r12, #4028]
	ldr r5, [r12, #3880]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3884]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3996]
	ldr r7, [r12, #4032]
	ldr r5, [r12, #3888]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3892]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4000]
	ldr r7, [r12, #4036]
	ldr r5, [r12, #3896]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3900]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4004]
	ldr r5, [r12, #3904]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3840]
	ldr r7, [r12, #3844]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3976]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3848]
	ldr r7, [r12, #3852]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3980]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3856]
	ldr r7, [r12, #3860]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3984]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3864]
	ldr r7, [r12, #3868]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3988]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3872]
	ldr r7, [r12, #3876]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3992]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3880]
	ldr r7, [r12, #3884]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3996]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r5, [r12, #3888]
	ldr r7, [r12, #3892]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4000]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #24]
	ldr r5, [r12, #3896]
	ldr r7, [r12, #3900]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4004]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #28]
	ldr r4, [r12, #4040]
	ldr r5, [r12, #4044]
	ldr r6, [r12, #4048]
	ldr r7, [r12, #4052]
	ldr r8, [r12, #4056]
	ldr r9, [r12, #4060]
	ldr lr, [r12, #4064]
	bx lr

vg_p224_sub_mod_p:
	mov r12, r0
	str r4, [r12, #4040]
	str r5, [r12, #4044]
	str r6, [r12, #4048]
	str r7, [r12, #4052]
	str r8, [r12, #4056]
	str r9, [r12, #4060]
	str lr, [r12, #4064]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #4008]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4012]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4016]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4020]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4024]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4028]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4032]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4036]
	add lr, r12, r1
	add r1, r12, r2
	add r2, r12, r3
	movw r6, #65535
	mov r3, #1
	ldr r7, [r1, #0]
	ldr r8, [r2, #0]
	ldr r9, [r12, #4008]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3840]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3844]
	lsr r3, r4, #16
	ldr r7, [r1, #4]
	ldr r8, [r2, #4]
	ldr r9, [r12, #4012]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3848]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3852]
	lsr r3, r4, #16
	ldr r7, [r1, #8]
	ldr r8, [r2, #8]
	ldr r9, [r12, #4016]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3856]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3860]
	lsr r3, r4, #16
	ldr r7, [r1, #12]
	ldr r8, [r2, #12]
	ldr r9, [r12, #4020]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3864]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3868]
	lsr r3, r4, #16
	ldr r7, [r1, #16]
	ldr r8, [r2, #16]
	ldr r9, [r12, #4024]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3872]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3876]
	lsr r3, r4, #16
	ldr r7, [r1, #20]
	ldr r8, [r2, #20]
	ldr r9, [r12, #4028]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3880]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3884]
	lsr r3, r4, #16
	ldr r7, [r1, #24]
	ldr r8, [r2, #24]
	ldr r9, [r12, #4032]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3888]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3892]
	lsr r3, r4, #16
	ldr r7, [r1, #28]
	ldr r8, [r2, #28]
	ldr r9, [r12, #4036]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3896]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3900]
	lsr r3, r4, #16
	sub r3, r3, #1
	str r3, [r12, #3904]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #4008]
	ldr r5, [r12, #3840]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3844]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3976]
	ldr r7, [r12, #4012]
	ldr r5, [r12, #3848]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3852]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3980]
	ldr r7, [r12, #4016]
	ldr r5, [r12, #3856]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3860]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3984]
	ldr r7, [r12, #4020]
	ldr r5, [r12, #3864]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3868]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3988]
	ldr r7, [r12, #4024]
	ldr r5, [r12, #3872]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3876]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3992]
	ldr r7, [r12, #4028]
	ldr r5, [r12, #3880]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3884]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3996]
	ldr r7, [r12, #4032]
	ldr r5, [r12, #3888]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3892]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4000]
	ldr r7, [r12, #4036]
	ldr r5, [r12, #3896]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3900]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4004]
	ldr r5, [r12, #3904]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3840]
	ldr r7, [r12, #3844]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3976]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3848]
	ldr r7, [r12, #3852]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3980]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3856]
	ldr r7, [r12, #3860]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3984]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3864]
	ldr r7, [r12, #3868]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3988]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3872]
	ldr r7, [r12, #3876]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3992]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3880]
	ldr r7, [r12, #3884]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3996]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r5, [r12, #3888]
	ldr r7, [r12, #3892]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4000]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #24]
	ldr r5, [r12, #3896]
	ldr r7, [r12, #3900]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4004]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #28]
	ldr r4, [r12, #4040]
	ldr r5, [r12, #4044]
	ldr r6, [r12, #4048]
	ldr r7, [r12, #4052]
	ldr r8, [r12, #4056]
	ldr r9, [r12, #4060]
	ldr lr, [r12, #4064]
	bx lr

vg_p224_mul_mod_n:
	mov r12, r0
	str r4, [r12, #4040]
	str r5, [r12, #4044]
	str r6, [r12, #4048]
	str r7, [r12, #4052]
	str r8, [r12, #4056]
	str r9, [r12, #4060]
	str lr, [r12, #4064]
	movw r4, #10813
	movt r4, #23644
	str r4, [r12, #4008]
	movw r4, #10565
	movt r4, #5085
	str r4, [r12, #4012]
	movw r4, #61502
	movt r4, #57528
	str r4, [r12, #4016]
	movw r4, #5794
	movt r4, #65535
	str r4, [r12, #4020]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4024]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4028]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4032]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4036]
	add lr, r12, r1
	add r1, r12, r2
	add r4, r12, r3
	mov r7, #0
	str r7, [r12, #3840]
	str r7, [r12, #3844]
	str r7, [r12, #3848]
	str r7, [r12, #3852]
	str r7, [r12, #3856]
	str r7, [r12, #3860]
	str r7, [r12, #3864]
	str r7, [r12, #3868]
	str r7, [r12, #3872]
	str r7, [r12, #3876]
	str r7, [r12, #3880]
	str r7, [r12, #3884]
	str r7, [r12, #3888]
	str r7, [r12, #3892]
	str r7, [r12, #3896]
	str r7, [r12, #3900]
	str r7, [r12, #3904]
	str r7, [r12, #3908]
	str r7, [r12, #3912]
	str r7, [r12, #3916]
	str r7, [r12, #3920]
	str r7, [r12, #3924]
	str r7, [r12, #3928]
	str r7, [r12, #3932]
	str r7, [r12, #3936]
	str r7, [r12, #3940]
	str r7, [r12, #3944]
	str r7, [r12, #3948]
	str r7, [r12, #3952]
	str r7, [r12, #3956]
	str r7, [r12, #3960]
	str r7, [r12, #3964]
	str r7, [r12, #3968]
	str r7, [r12, #3972]
	movw r6, #65535
	mov r0, r12
	mov r1, r1
	mov r9, #8
20:
	ldr r8, [r1, #0]
	and r2, r8, r6
	mov r3, #0
	ldr r7, [r4, #0]
	and r7, r7, r6
	ldr r5, [r0, #3840]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3840]
	lsr r3, r5, #16
	ldr r7, [r4, #0]
	lsr r7, r7, #16
	ldr r5, [r0, #3844]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3844]
	lsr r3, r5, #16
	ldr r7, [r4, #4]
	and r7, r7, r6
	ldr r5, [r0, #3848]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3848]
	lsr r3, r5, #16
	ldr r7, [r4, #4]
	lsr r7, r7, #16
	ldr r5, [r0, #3852]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3852]
	lsr r3, r5, #16
	ldr r7, [r4, #8]
	and r7, r7, r6
	ldr r5, [r0, #3856]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3856]
	lsr r3, r5, #16
	ldr r7, [r4, #8]
	lsr r7, r7, #16
	ldr r5, [r0, #3860]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3860]
	lsr r3, r5, #16
	ldr r7, [r4, #12]
	and r7, r7, r6
	ldr r5, [r0, #3864]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3864]
	lsr r3, r5, #16
	ldr r7, [r4, #12]
	lsr r7, r7, #16
	ldr r5, [r0, #3868]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3868]
	lsr r3, r5, #16
	ldr r7, [r4, #16]
	and r7, r7, r6
	ldr r5, [r0, #3872]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3872]
	lsr r3, r5, #16
	ldr r7, [r4, #16]
	lsr r7, r7, #16
	ldr r5, [r0, #3876]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3876]
	lsr r3, r5, #16
	ldr r7, [r4, #20]
	and r7, r7, r6
	ldr r5, [r0, #3880]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3880]
	lsr r3, r5, #16
	ldr r7, [r4, #20]
	lsr r7, r7, #16
	ldr r5, [r0, #3884]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3884]
	lsr r3, r5, #16
	ldr r7, [r4, #24]
	and r7, r7, r6
	ldr r5, [r0, #3888]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3888]
	lsr r3, r5, #16
	ldr r7, [r4, #24]
	lsr r7, r7, #16
	ldr r5, [r0, #3892]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3892]
	lsr r3, r5, #16
	ldr r7, [r4, #28]
	and r7, r7, r6
	ldr r5, [r0, #3896]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3896]
	lsr r3, r5, #16
	ldr r7, [r4, #28]
	lsr r7, r7, #16
	ldr r5, [r0, #3900]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3900]
	lsr r3, r5, #16
	ldr r5, [r0, #3904]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3904]
	ldr r7, [r0, #3908]
	add r7, r7, r5, lsr #16
	str r7, [r0, #3908]
	ldr r2, [r0, #3840]
	movw r7, #49899
	mul r2, r2, r7
	and r2, r2, r6
	mov r3, #0
	ldr r7, [r12, #4008]
	and r7, r7, r6
	ldr r5, [r0, #3840]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3840]
	lsr r3, r5, #16
	ldr r7, [r12, #4008]
	lsr r7, r7, #16
	ldr r5, [r0, #3844]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3844]
	lsr r3, r5, #16
	ldr r7, [r12, #4012]
	and r7, r7, r6
	ldr r5, [r0, #3848]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3848]
	lsr r3, r5, #16
	ldr r7, [r12, #4012]
	lsr r7, r7, #16
	ldr r5, [r0, #3852]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3852]
	lsr r3, r5, #16
	ldr r7, [r12, #4016]
	and r7, r7, r6
	ldr r5, [r0, #3856]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3856]
	lsr r3, r5, #16
	ldr r7, [r12, #4016]
	lsr r7, r7, #16
	ldr r5, [r0, #3860]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3860]
	lsr r3, r5, #16
	ldr r7, [r12, #4020]
	and r7, r7, r6
	ldr r5, [r0, #3864]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3864]
	lsr r3, r5, #16
	ldr r7, [r12, #4020]
	lsr r7, r7, #16
	ldr r5, [r0, #3868]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3868]
	lsr r3, r5, #16
	ldr r7, [r12, #4024]
	and r7, r7, r6
	ldr r5, [r0, #3872]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3872]
	lsr r3, r5, #16
	ldr r7, [r12, #4024]
	lsr r7, r7, #16
	ldr r5, [r0, #3876]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3876]
	lsr r3, r5, #16
	ldr r7, [r12, #4028]
	and r7, r7, r6
	ldr r5, [r0, #3880]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3880]
	lsr r3, r5, #16
	ldr r7, [r12, #4028]
	lsr r7, r7, #16
	ldr r5, [r0, #3884]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3884]
	lsr r3, r5, #16
	ldr r7, [r12, #4032]
	and r7, r7, r6
	ldr r5, [r0, #3888]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3888]
	lsr r3, r5, #16
	ldr r7, [r12, #4032]
	lsr r7, r7, #16
	ldr r5, [r0, #3892]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3892]
	lsr r3, r5, #16
	ldr r7, [r12, #4036]
	and r7, r7, r6
	ldr r5, [r0, #3896]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3896]
	lsr r3, r5, #16
	ldr r7, [r12, #4036]
	lsr r7, r7, #16
	ldr r5, [r0, #3900]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3900]
	lsr r3, r5, #16
	ldr r5, [r0, #3904]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3904]
	ldr r7, [r0, #3908]
	add r7, r7, r5, lsr #16
	str r7, [r0, #3908]
	add r0, r0, #4
	lsr r2, r8, #16
	mov r3, #0
	ldr r7, [r4, #0]
	and r7, r7, r6
	ldr r5, [r0, #3840]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3840]
	lsr r3, r5, #16
	ldr r7, [r4, #0]
	lsr r7, r7, #16
	ldr r5, [r0, #3844]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3844]
	lsr r3, r5, #16
	ldr r7, [r4, #4]
	and r7, r7, r6
	ldr r5, [r0, #3848]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3848]
	lsr r3, r5, #16
	ldr r7, [r4, #4]
	lsr r7, r7, #16
	ldr r5, [r0, #3852]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3852]
	lsr r3, r5, #16
	ldr r7, [r4, #8]
	and r7, r7, r6
	ldr r5, [r0, #3856]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3856]
	lsr r3, r5, #16
	ldr r7, [r4, #8]
	lsr r7, r7, #16
	ldr r5, [r0, #3860]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3860]
	lsr r3, r5, #16
	ldr r7, [r4, #12]
	and r7, r7, r6
	ldr r5, [r0, #3864]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3864]
	lsr r3, r5, #16
	ldr r7, [r4, #12]
	lsr r7, r7, #16
	ldr r5, [r0, #3868]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3868]
	lsr r3, r5, #16
	ldr r7, [r4, #16]
	and r7, r7, r6
	ldr r5, [r0, #3872]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3872]
	lsr r3, r5, #16
	ldr r7, [r4, #16]
	lsr r7, r7, #16
	ldr r5, [r0, #3876]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3876]
	lsr r3, r5, #16
	ldr r7, [r4, #20]
	and r7, r7, r6
	ldr r5, [r0, #3880]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3880]
	lsr r3, r5, #16
	ldr r7, [r4, #20]
	lsr r7, r7, #16
	ldr r5, [r0, #3884]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3884]
	lsr r3, r5, #16
	ldr r7, [r4, #24]
	and r7, r7, r6
	ldr r5, [r0, #3888]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3888]
	lsr r3, r5, #16
	ldr r7, [r4, #24]
	lsr r7, r7, #16
	ldr r5, [r0, #3892]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3892]
	lsr r3, r5, #16
	ldr r7, [r4, #28]
	and r7, r7, r6
	ldr r5, [r0, #3896]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3896]
	lsr r3, r5, #16
	ldr r7, [r4, #28]
	lsr r7, r7, #16
	ldr r5, [r0, #3900]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3900]
	lsr r3, r5, #16
	ldr r5, [r0, #3904]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3904]
	ldr r7, [r0, #3908]
	add r7, r7, r5, lsr #16
	str r7, [r0, #3908]
	ldr r2, [r0, #3840]
	movw r7, #49899
	mul r2, r2, r7
	and r2, r2, r6
	mov r3, #0
	ldr r7, [r12, #4008]
	and r7, r7, r6
	ldr r5, [r0, #3840]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3840]
	lsr r3, r5, #16
	ldr r7, [r12, #4008]
	lsr r7, r7, #16
	ldr r5, [r0, #3844]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3844]
	lsr r3, r5, #16
	ldr r7, [r12, #4012]
	and r7, r7, r6
	ldr r5, [r0, #3848]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3848]
	lsr r3, r5, #16
	ldr r7, [r12, #4012]
	lsr r7, r7, #16
	ldr r5, [r0, #3852]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3852]
	lsr r3, r5, #16
	ldr r7, [r12, #4016]
	and r7, r7, r6
	ldr r5, [r0, #3856]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3856]
	lsr r3, r5, #16
	ldr r7, [r12, #4016]
	lsr r7, r7, #16
	ldr r5, [r0, #3860]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3860]
	lsr r3, r5, #16
	ldr r7, [r12, #4020]
	and r7, r7, r6
	ldr r5, [r0, #3864]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3864]
	lsr r3, r5, #16
	ldr r7, [r12, #4020]
	lsr r7, r7, #16
	ldr r5, [r0, #3868]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3868]
	lsr r3, r5, #16
	ldr r7, [r12, #4024]
	and r7, r7, r6
	ldr r5, [r0, #3872]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3872]
	lsr r3, r5, #16
	ldr r7, [r12, #4024]
	lsr r7, r7, #16
	ldr r5, [r0, #3876]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3876]
	lsr r3, r5, #16
	ldr r7, [r12, #4028]
	and r7, r7, r6
	ldr r5, [r0, #3880]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3880]
	lsr r3, r5, #16
	ldr r7, [r12, #4028]
	lsr r7, r7, #16
	ldr r5, [r0, #3884]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3884]
	lsr r3, r5, #16
	ldr r7, [r12, #4032]
	and r7, r7, r6
	ldr r5, [r0, #3888]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3888]
	lsr r3, r5, #16
	ldr r7, [r12, #4032]
	lsr r7, r7, #16
	ldr r5, [r0, #3892]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3892]
	lsr r3, r5, #16
	ldr r7, [r12, #4036]
	and r7, r7, r6
	ldr r5, [r0, #3896]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3896]
	lsr r3, r5, #16
	ldr r7, [r12, #4036]
	lsr r7, r7, #16
	ldr r5, [r0, #3900]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3900]
	lsr r3, r5, #16
	ldr r5, [r0, #3904]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3904]
	ldr r7, [r0, #3908]
	add r7, r7, r5, lsr #16
	str r7, [r0, #3908]
	add r0, r0, #4
	add r1, r1, #4
	subs r9, r9, #1
	bne 20b
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #4008]
	ldr r5, [r12, #3904]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3908]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3976]
	ldr r7, [r12, #4012]
	ldr r5, [r12, #3912]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3916]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3980]
	ldr r7, [r12, #4016]
	ldr r5, [r12, #3920]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3924]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3984]
	ldr r7, [r12, #4020]
	ldr r5, [r12, #3928]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3932]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3988]
	ldr r7, [r12, #4024]
	ldr r5, [r12, #3936]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3940]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3992]
	ldr r7, [r12, #4028]
	ldr r5, [r12, #3944]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3948]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3996]
	ldr r7, [r12, #4032]
	ldr r5, [r12, #3952]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3956]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4000]
	ldr r7, [r12, #4036]
	ldr r5, [r12, #3960]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3964]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4004]
	ldr r5, [r12, #3968]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3904]
	ldr r7, [r12, #3908]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3976]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3912]
	ldr r7, [r12, #3916]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3980]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3920]
	ldr r7, [r12, #3924]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3984]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3928]
	ldr r7, [r12, #3932]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3988]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3936]
	ldr r7, [r12, #3940]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3992]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3944]
	ldr r7, [r12, #3948]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3996]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r5, [r12, #3952]
	ldr r7, [r12, #3956]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4000]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #24]
	ldr r5, [r12, #3960]
	ldr r7, [r12, #3964]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4004]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #28]
	ldr r4, [r12, #4040]
	ldr r5, [r12, #4044]
	ldr r6, [r12, #4048]
	ldr r7, [r12, #4052]
	ldr r8, [r12, #4056]
	ldr r9, [r12, #4060]
	ldr lr, [r12, #4064]
	bx lr

vg_p224_mul_mod_n_umaal:
	mov r12, r0
	str r4, [r12, #4040]
	str r5, [r12, #4044]
	str r6, [r12, #4048]
	str r7, [r12, #4052]
	str r8, [r12, #4056]
	str r9, [r12, #4060]
	str lr, [r12, #4064]
	movw r4, #10813
	movt r4, #23644
	str r4, [r12, #4008]
	movw r4, #10565
	movt r4, #5085
	str r4, [r12, #4012]
	movw r4, #61502
	movt r4, #57528
	str r4, [r12, #4016]
	movw r4, #5794
	movt r4, #65535
	str r4, [r12, #4020]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4024]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4028]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4032]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4036]
	add lr, r12, r1
	add r1, r12, r2
	add r4, r12, r3
	mov r7, #0
	str r7, [r12, #3840]
	str r7, [r12, #3844]
	str r7, [r12, #3848]
	str r7, [r12, #3852]
	str r7, [r12, #3856]
	str r7, [r12, #3860]
	str r7, [r12, #3864]
	str r7, [r12, #3868]
	str r7, [r12, #3872]
	str r7, [r12, #3876]
	mov r9, #8
20:
	ldr r2, [r1, #0]
	mov r3, #0
	ldr r7, [r4, #0]
	ldr r5, [r12, #3840]
	umaal r5, r3, r2, r7
	str r5, [r12, #3840]
	ldr r7, [r4, #4]
	ldr r5, [r12, #3844]
	umaal r5, r3, r2, r7
	str r5, [r12, #3844]
	ldr r7, [r4, #8]
	ldr r5, [r12, #3848]
	umaal r5, r3, r2, r7
	str r5, [r12, #3848]
	ldr r7, [r4, #12]
	ldr r5, [r12, #3852]
	umaal r5, r3, r2, r7
	str r5, [r12, #3852]
	ldr r7, [r4, #16]
	ldr r5, [r12, #3856]
	umaal r5, r3, r2, r7
	str r5, [r12, #3856]
	ldr r7, [r4, #20]
	ldr r5, [r12, #3860]
	umaal r5, r3, r2, r7
	str r5, [r12, #3860]
	ldr r7, [r4, #24]
	ldr r5, [r12, #3864]
	umaal r5, r3, r2, r7
	str r5, [r12, #3864]
	ldr r7, [r4, #28]
	ldr r5, [r12, #3868]
	umaal r5, r3, r2, r7
	str r5, [r12, #3868]
	ldr r5, [r12, #3872]
	ldr r6, [r12, #3876]
	adds r5, r5, r3
	adc r6, r6, #0
	str r5, [r12, #3872]
	str r6, [r12, #3876]
	ldr r2, [r12, #3840]
	movw r7, #49899
	movt r7, #27167
	mul r2, r2, r7
	mov r3, #0
	ldr r7, [r12, #4008]
	ldr r5, [r12, #3840]
	umaal r5, r3, r2, r7
	str r5, [r12, #3840]
	ldr r7, [r12, #4012]
	ldr r5, [r12, #3844]
	umaal r5, r3, r2, r7
	str r5, [r12, #3844]
	ldr r7, [r12, #4016]
	ldr r5, [r12, #3848]
	umaal r5, r3, r2, r7
	str r5, [r12, #3848]
	ldr r7, [r12, #4020]
	ldr r5, [r12, #3852]
	umaal r5, r3, r2, r7
	str r5, [r12, #3852]
	ldr r7, [r12, #4024]
	ldr r5, [r12, #3856]
	umaal r5, r3, r2, r7
	str r5, [r12, #3856]
	ldr r7, [r12, #4028]
	ldr r5, [r12, #3860]
	umaal r5, r3, r2, r7
	str r5, [r12, #3860]
	ldr r7, [r12, #4032]
	ldr r5, [r12, #3864]
	umaal r5, r3, r2, r7
	str r5, [r12, #3864]
	ldr r7, [r12, #4036]
	ldr r5, [r12, #3868]
	umaal r5, r3, r2, r7
	str r5, [r12, #3868]
	ldr r5, [r12, #3872]
	ldr r6, [r12, #3876]
	adds r5, r5, r3
	adc r6, r6, #0
	str r5, [r12, #3872]
	str r6, [r12, #3876]
	ldr r5, [r12, #3844]
	str r5, [r12, #3840]
	ldr r5, [r12, #3848]
	str r5, [r12, #3844]
	ldr r5, [r12, #3852]
	str r5, [r12, #3848]
	ldr r5, [r12, #3856]
	str r5, [r12, #3852]
	ldr r5, [r12, #3860]
	str r5, [r12, #3856]
	ldr r5, [r12, #3864]
	str r5, [r12, #3860]
	ldr r5, [r12, #3868]
	str r5, [r12, #3864]
	ldr r5, [r12, #3872]
	str r5, [r12, #3868]
	ldr r5, [r12, #3876]
	str r5, [r12, #3872]
	mov r5, #0
	str r5, [r12, #3876]
	add r1, r1, #4
	subs r9, r9, #1
	bne 20b
	movw r6, #65535
	ldr r7, [r12, #3840]
	and r7, r7, r6
	str r7, [r12, #3880]
	ldr r7, [r12, #3840]
	lsr r7, r7, #16
	str r7, [r12, #3884]
	ldr r7, [r12, #3844]
	and r7, r7, r6
	str r7, [r12, #3888]
	ldr r7, [r12, #3844]
	lsr r7, r7, #16
	str r7, [r12, #3892]
	ldr r7, [r12, #3848]
	and r7, r7, r6
	str r7, [r12, #3896]
	ldr r7, [r12, #3848]
	lsr r7, r7, #16
	str r7, [r12, #3900]
	ldr r7, [r12, #3852]
	and r7, r7, r6
	str r7, [r12, #3904]
	ldr r7, [r12, #3852]
	lsr r7, r7, #16
	str r7, [r12, #3908]
	ldr r7, [r12, #3856]
	and r7, r7, r6
	str r7, [r12, #3912]
	ldr r7, [r12, #3856]
	lsr r7, r7, #16
	str r7, [r12, #3916]
	ldr r7, [r12, #3860]
	and r7, r7, r6
	str r7, [r12, #3920]
	ldr r7, [r12, #3860]
	lsr r7, r7, #16
	str r7, [r12, #3924]
	ldr r7, [r12, #3864]
	and r7, r7, r6
	str r7, [r12, #3928]
	ldr r7, [r12, #3864]
	lsr r7, r7, #16
	str r7, [r12, #3932]
	ldr r7, [r12, #3868]
	and r7, r7, r6
	str r7, [r12, #3936]
	ldr r7, [r12, #3868]
	lsr r7, r7, #16
	str r7, [r12, #3940]
	ldr r7, [r12, #3872]
	and r7, r7, r6
	str r7, [r12, #3944]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #4008]
	ldr r5, [r12, #3880]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3884]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3976]
	ldr r7, [r12, #4012]
	ldr r5, [r12, #3888]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3892]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3980]
	ldr r7, [r12, #4016]
	ldr r5, [r12, #3896]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3900]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3984]
	ldr r7, [r12, #4020]
	ldr r5, [r12, #3904]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3908]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3988]
	ldr r7, [r12, #4024]
	ldr r5, [r12, #3912]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3916]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3992]
	ldr r7, [r12, #4028]
	ldr r5, [r12, #3920]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3924]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3996]
	ldr r7, [r12, #4032]
	ldr r5, [r12, #3928]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3932]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4000]
	ldr r7, [r12, #4036]
	ldr r5, [r12, #3936]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3940]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4004]
	ldr r5, [r12, #3944]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3880]
	ldr r7, [r12, #3884]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3976]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3888]
	ldr r7, [r12, #3892]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3980]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3896]
	ldr r7, [r12, #3900]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3984]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3904]
	ldr r7, [r12, #3908]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3988]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3912]
	ldr r7, [r12, #3916]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3992]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3920]
	ldr r7, [r12, #3924]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3996]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r5, [r12, #3928]
	ldr r7, [r12, #3932]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4000]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #24]
	ldr r5, [r12, #3936]
	ldr r7, [r12, #3940]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4004]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #28]
	ldr r4, [r12, #4040]
	ldr r5, [r12, #4044]
	ldr r6, [r12, #4048]
	ldr r7, [r12, #4052]
	ldr r8, [r12, #4056]
	ldr r9, [r12, #4060]
	ldr lr, [r12, #4064]
	bx lr

vg_p224_add_mod_n:
	mov r12, r0
	str r4, [r12, #4040]
	str r5, [r12, #4044]
	str r6, [r12, #4048]
	str r7, [r12, #4052]
	str r8, [r12, #4056]
	str r9, [r12, #4060]
	str lr, [r12, #4064]
	movw r4, #10813
	movt r4, #23644
	str r4, [r12, #4008]
	movw r4, #10565
	movt r4, #5085
	str r4, [r12, #4012]
	movw r4, #61502
	movt r4, #57528
	str r4, [r12, #4016]
	movw r4, #5794
	movt r4, #65535
	str r4, [r12, #4020]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4024]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4028]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4032]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4036]
	add lr, r12, r1
	add r1, r12, r2
	add r2, r12, r3
	movw r6, #65535
	mov r3, #0
	ldr r7, [r1, #0]
	ldr r8, [r2, #0]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3840]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3844]
	lsr r3, r4, #16
	ldr r7, [r1, #4]
	ldr r8, [r2, #4]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3848]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3852]
	lsr r3, r4, #16
	ldr r7, [r1, #8]
	ldr r8, [r2, #8]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3856]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3860]
	lsr r3, r4, #16
	ldr r7, [r1, #12]
	ldr r8, [r2, #12]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3864]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3868]
	lsr r3, r4, #16
	ldr r7, [r1, #16]
	ldr r8, [r2, #16]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3872]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3876]
	lsr r3, r4, #16
	ldr r7, [r1, #20]
	ldr r8, [r2, #20]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3880]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3884]
	lsr r3, r4, #16
	ldr r7, [r1, #24]
	ldr r8, [r2, #24]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3888]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3892]
	lsr r3, r4, #16
	ldr r7, [r1, #28]
	ldr r8, [r2, #28]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3896]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3900]
	lsr r3, r4, #16
	str r3, [r12, #3904]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #4008]
	ldr r5, [r12, #3840]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3844]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3976]
	ldr r7, [r12, #4012]
	ldr r5, [r12, #3848]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3852]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3980]
	ldr r7, [r12, #4016]
	ldr r5, [r12, #3856]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3860]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3984]
	ldr r7, [r12, #4020]
	ldr r5, [r12, #3864]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3868]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3988]
	ldr r7, [r12, #4024]
	ldr r5, [r12, #3872]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3876]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3992]
	ldr r7, [r12, #4028]
	ldr r5, [r12, #3880]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3884]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3996]
	ldr r7, [r12, #4032]
	ldr r5, [r12, #3888]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3892]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4000]
	ldr r7, [r12, #4036]
	ldr r5, [r12, #3896]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3900]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4004]
	ldr r5, [r12, #3904]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3840]
	ldr r7, [r12, #3844]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3976]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3848]
	ldr r7, [r12, #3852]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3980]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3856]
	ldr r7, [r12, #3860]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3984]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3864]
	ldr r7, [r12, #3868]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3988]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3872]
	ldr r7, [r12, #3876]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3992]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3880]
	ldr r7, [r12, #3884]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3996]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r5, [r12, #3888]
	ldr r7, [r12, #3892]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4000]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #24]
	ldr r5, [r12, #3896]
	ldr r7, [r12, #3900]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4004]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #28]
	ldr r4, [r12, #4040]
	ldr r5, [r12, #4044]
	ldr r6, [r12, #4048]
	ldr r7, [r12, #4052]
	ldr r8, [r12, #4056]
	ldr r9, [r12, #4060]
	ldr lr, [r12, #4064]
	bx lr

vg_p224_sub_mod_n:
	mov r12, r0
	str r4, [r12, #4040]
	str r5, [r12, #4044]
	str r6, [r12, #4048]
	str r7, [r12, #4052]
	str r8, [r12, #4056]
	str r9, [r12, #4060]
	str lr, [r12, #4064]
	movw r4, #10813
	movt r4, #23644
	str r4, [r12, #4008]
	movw r4, #10565
	movt r4, #5085
	str r4, [r12, #4012]
	movw r4, #61502
	movt r4, #57528
	str r4, [r12, #4016]
	movw r4, #5794
	movt r4, #65535
	str r4, [r12, #4020]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4024]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4028]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4032]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #4036]
	add lr, r12, r1
	add r1, r12, r2
	add r2, r12, r3
	movw r6, #65535
	mov r3, #1
	ldr r7, [r1, #0]
	ldr r8, [r2, #0]
	ldr r9, [r12, #4008]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3840]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3844]
	lsr r3, r4, #16
	ldr r7, [r1, #4]
	ldr r8, [r2, #4]
	ldr r9, [r12, #4012]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3848]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3852]
	lsr r3, r4, #16
	ldr r7, [r1, #8]
	ldr r8, [r2, #8]
	ldr r9, [r12, #4016]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3856]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3860]
	lsr r3, r4, #16
	ldr r7, [r1, #12]
	ldr r8, [r2, #12]
	ldr r9, [r12, #4020]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3864]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3868]
	lsr r3, r4, #16
	ldr r7, [r1, #16]
	ldr r8, [r2, #16]
	ldr r9, [r12, #4024]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3872]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3876]
	lsr r3, r4, #16
	ldr r7, [r1, #20]
	ldr r8, [r2, #20]
	ldr r9, [r12, #4028]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3880]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3884]
	lsr r3, r4, #16
	ldr r7, [r1, #24]
	ldr r8, [r2, #24]
	ldr r9, [r12, #4032]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3888]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3892]
	lsr r3, r4, #16
	ldr r7, [r1, #28]
	ldr r8, [r2, #28]
	ldr r9, [r12, #4036]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3896]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3900]
	lsr r3, r4, #16
	sub r3, r3, #1
	str r3, [r12, #3904]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #4008]
	ldr r5, [r12, #3840]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3844]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3976]
	ldr r7, [r12, #4012]
	ldr r5, [r12, #3848]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3852]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3980]
	ldr r7, [r12, #4016]
	ldr r5, [r12, #3856]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3860]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3984]
	ldr r7, [r12, #4020]
	ldr r5, [r12, #3864]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3868]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3988]
	ldr r7, [r12, #4024]
	ldr r5, [r12, #3872]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3876]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3992]
	ldr r7, [r12, #4028]
	ldr r5, [r12, #3880]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3884]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3996]
	ldr r7, [r12, #4032]
	ldr r5, [r12, #3888]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3892]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4000]
	ldr r7, [r12, #4036]
	ldr r5, [r12, #3896]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3900]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4004]
	ldr r5, [r12, #3904]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3840]
	ldr r7, [r12, #3844]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3976]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3848]
	ldr r7, [r12, #3852]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3980]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3856]
	ldr r7, [r12, #3860]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3984]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3864]
	ldr r7, [r12, #3868]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3988]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3872]
	ldr r7, [r12, #3876]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3992]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3880]
	ldr r7, [r12, #3884]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3996]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r5, [r12, #3888]
	ldr r7, [r12, #3892]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4000]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #24]
	ldr r5, [r12, #3896]
	ldr r7, [r12, #3900]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4004]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #28]
	ldr r4, [r12, #4040]
	ldr r5, [r12, #4044]
	ldr r6, [r12, #4048]
	ldr r7, [r12, #4052]
	ldr r8, [r12, #4056]
	ldr r9, [r12, #4060]
	ldr lr, [r12, #4064]
	bx lr
