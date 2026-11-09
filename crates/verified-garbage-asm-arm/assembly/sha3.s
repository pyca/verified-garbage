// The functions of `src/sha3.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha3_224_update:
	sub sp, sp, #16
	add r12, sp, #0
	str lr, [r12, #8]
	str r3, [r12, #0]
	ldr lr, [sp, #16]
	str lr, [r12, #4]
	mov r3, r2
	mov r2, r1
	mov r1, #144
	bl {vg_keccak_absorb_scratch}
	ldr lr, [sp, #8]
	add sp, sp, #16
	bx lr

vg_sha3_224_finalize:
	sub sp, sp, #664
	add r12, sp, #0
	str lr, [r12, #8]
	str r0, [r12, #12]
	str r2, [r12, #16]
	add lr, sp, #24
	str lr, [r12, #0]
	mov r2, r1
	mov r1, #144
	mov r3, #6
	bl {vg_keccak_pad_scratch}
	add r12, sp, #0
	ldr r0, [sp, #12]
	ldr r3, [sp, #16]
	mov r1, #144
	mov r2, #0
	mov lr, #28
	str lr, [r12, #0]
	add lr, sp, #24
	str lr, [r12, #4]
	bl {vg_keccak_squeeze_scratch}
	ldr lr, [sp, #8]
	add sp, sp, #664
	bx lr

vg_sha3_256_update:
	sub sp, sp, #16
	add r12, sp, #0
	str lr, [r12, #8]
	str r3, [r12, #0]
	ldr lr, [sp, #16]
	str lr, [r12, #4]
	mov r3, r2
	mov r2, r1
	mov r1, #136
	bl {vg_keccak_absorb_scratch}
	ldr lr, [sp, #8]
	add sp, sp, #16
	bx lr

vg_sha3_256_finalize:
	sub sp, sp, #664
	add r12, sp, #0
	str lr, [r12, #8]
	str r0, [r12, #12]
	str r2, [r12, #16]
	add lr, sp, #24
	str lr, [r12, #0]
	mov r2, r1
	mov r1, #136
	mov r3, #6
	bl {vg_keccak_pad_scratch}
	add r12, sp, #0
	ldr r0, [sp, #12]
	ldr r3, [sp, #16]
	mov r1, #136
	mov r2, #0
	mov lr, #32
	str lr, [r12, #0]
	add lr, sp, #24
	str lr, [r12, #4]
	bl {vg_keccak_squeeze_scratch}
	ldr lr, [sp, #8]
	add sp, sp, #664
	bx lr

vg_sha3_384_update:
	sub sp, sp, #16
	add r12, sp, #0
	str lr, [r12, #8]
	str r3, [r12, #0]
	ldr lr, [sp, #16]
	str lr, [r12, #4]
	mov r3, r2
	mov r2, r1
	mov r1, #104
	bl {vg_keccak_absorb_scratch}
	ldr lr, [sp, #8]
	add sp, sp, #16
	bx lr

vg_sha3_384_finalize:
	sub sp, sp, #664
	add r12, sp, #0
	str lr, [r12, #8]
	str r0, [r12, #12]
	str r2, [r12, #16]
	add lr, sp, #24
	str lr, [r12, #0]
	mov r2, r1
	mov r1, #104
	mov r3, #6
	bl {vg_keccak_pad_scratch}
	add r12, sp, #0
	ldr r0, [sp, #12]
	ldr r3, [sp, #16]
	mov r1, #104
	mov r2, #0
	mov lr, #48
	str lr, [r12, #0]
	add lr, sp, #24
	str lr, [r12, #4]
	bl {vg_keccak_squeeze_scratch}
	ldr lr, [sp, #8]
	add sp, sp, #664
	bx lr

vg_sha3_512_update:
	sub sp, sp, #16
	add r12, sp, #0
	str lr, [r12, #8]
	str r3, [r12, #0]
	ldr lr, [sp, #16]
	str lr, [r12, #4]
	mov r3, r2
	mov r2, r1
	mov r1, #72
	bl {vg_keccak_absorb_scratch}
	ldr lr, [sp, #8]
	add sp, sp, #16
	bx lr

vg_sha3_512_finalize:
	sub sp, sp, #664
	add r12, sp, #0
	str lr, [r12, #8]
	str r0, [r12, #12]
	str r2, [r12, #16]
	add lr, sp, #24
	str lr, [r12, #0]
	mov r2, r1
	mov r1, #72
	mov r3, #6
	bl {vg_keccak_pad_scratch}
	add r12, sp, #0
	ldr r0, [sp, #12]
	ldr r3, [sp, #16]
	mov r1, #72
	mov r2, #0
	mov lr, #64
	str lr, [r12, #0]
	add lr, sp, #24
	str lr, [r12, #4]
	bl {vg_keccak_squeeze_scratch}
	ldr lr, [sp, #8]
	add sp, sp, #664
	bx lr

vg_shake128_update:
	sub sp, sp, #16
	add r12, sp, #0
	str lr, [r12, #8]
	str r3, [r12, #0]
	ldr lr, [sp, #16]
	str lr, [r12, #4]
	mov r3, r2
	mov r2, r1
	mov r1, #168
	bl {vg_keccak_absorb_scratch}
	ldr lr, [sp, #8]
	add sp, sp, #16
	bx lr

vg_shake128_finalize:
	sub sp, sp, #648
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	mov r2, r1
	mov r1, #168
	mov r3, #31
	bl {vg_keccak_pad_scratch}
	ldr lr, [sp, #4]
	add sp, sp, #648
	bx lr

vg_shake128_squeeze:
	sub sp, sp, #656
	add r12, sp, #0
	str lr, [r12, #8]
	str r3, [r12, #0]
	add lr, sp, #16
	str lr, [r12, #4]
	mov r3, r2
	mov r2, r1
	mov r1, #168
	bl {vg_keccak_squeeze_scratch}
	ldr lr, [sp, #8]
	add sp, sp, #656
	bx lr

vg_shake256_finalize:
	sub sp, sp, #648
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	mov r2, r1
	mov r1, #136
	mov r3, #31
	bl {vg_keccak_pad_scratch}
	ldr lr, [sp, #4]
	add sp, sp, #648
	bx lr

vg_shake256_squeeze:
	sub sp, sp, #656
	add r12, sp, #0
	str lr, [r12, #8]
	str r3, [r12, #0]
	add lr, sp, #16
	str lr, [r12, #4]
	mov r3, r2
	mov r2, r1
	mov r1, #136
	bl {vg_keccak_squeeze_scratch}
	ldr lr, [sp, #8]
	add sp, sp, #656
	bx lr
