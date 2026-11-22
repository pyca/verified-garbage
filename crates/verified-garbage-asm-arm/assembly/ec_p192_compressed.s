// The functions of `src/ec_p192_compressed.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p192_compress_public_key:
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
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #808]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #812]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #816]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #820]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #824]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #828]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #832]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #836]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #840]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #844]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #848]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #852]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #856]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #860]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #864]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #868]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #872]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #876]
	movw r10, #:lower16:({VG_P192_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P192_FRAME_CONSTS}
2:
	add r10, pc
3:
	mov r11, #51
20:
	sub r11, r11, #1
	add r5, r10, r11, lsl #3
	ldr r4, [r5, #0]
	ldr r5, [r5, #4]
	add r9, r12, r11, lsl #3
	str r4, [r9, #64]
	str r5, [r9, #68]
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1120]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1000]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1004]
	movw r4, #2
	movt r4, #0
	str r4, [r12, #1008]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1012]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1016]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1020]
	movw r4, #15000
	movt r4, #42723
	str r4, [r12, #1024]
	movw r4, #58374
	movt r4, #25305
	str r4, [r12, #1028]
	movw r4, #27362
	movt r4, #6407
	str r4, [r12, #1032]
	movw r4, #52658
	movt r4, #29313
	str r4, [r12, #1036]
	movw r4, #45361
	movt r4, #22464
	str r4, [r12, #1040]
	movw r4, #61125
	movt r4, #29640
	str r4, [r12, #1044]
	add r6, r1, #1
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #856]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #860]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #864]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #868]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #872]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #876]
	add r6, r6, #24
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #928]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #932]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #936]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #940]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #944]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #948]
	ldrb r4, [r1, #0]
	eor r4, r4, #4
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #856]
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
	ldr r7, [r12, #860]
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
	ldr r7, [r12, #864]
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
	ldr r7, [r12, #868]
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
	ldr r7, [r12, #872]
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
	ldr r7, [r12, #876]
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
	sub r5, r3, #1
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #928]
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
	ldr r7, [r12, #932]
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
	ldr r7, [r12, #936]
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
	ldr r7, [r12, #940]
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
	ldr r7, [r12, #944]
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
	ldr r7, [r12, #948]
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
	sub r5, r3, #1
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	mov r10, lr
	mov r0, r12
	movw r1, #880
	movw r2, #856
	movw r3, #1000
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #928
	movw r3, #1000
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #952
	movw r2, #904
	movw r3, #904
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #880
	movw r3, #880
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1072
	movw r2, #1048
	movw r3, #880
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #208
	movw r3, #880
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #976
	movw r2, #1072
	movw r3, #1048
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1072
	movw r2, #976
	movw r3, #1024
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #952
	movw r3, #1072
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #1048]
	ldr r4, [r12, #1052]
	orr r5, r5, r4
	ldr r4, [r12, #1056]
	orr r5, r5, r4
	ldr r4, [r12, #1060]
	orr r5, r5, r4
	ldr r4, [r12, #1064]
	orr r5, r5, r4
	ldr r4, [r12, #1068]
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
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	ldr r10, [r12, #1120]
	ldr r4, [r12, #256]
	ldr r5, [r12, #880]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #976]
	ldr r4, [r12, #260]
	ldr r5, [r12, #884]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #980]
	ldr r4, [r12, #264]
	ldr r5, [r12, #888]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #984]
	ldr r4, [r12, #268]
	ldr r5, [r12, #892]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #988]
	ldr r4, [r12, #272]
	ldr r5, [r12, #896]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #992]
	ldr r4, [r12, #276]
	ldr r5, [r12, #900]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #996]
	ldr r4, [r12, #280]
	ldr r5, [r12, #904]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1096]
	ldr r4, [r12, #284]
	ldr r5, [r12, #908]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1100]
	ldr r4, [r12, #288]
	ldr r5, [r12, #912]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1104]
	ldr r4, [r12, #292]
	ldr r5, [r12, #916]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1108]
	ldr r4, [r12, #296]
	ldr r5, [r12, #920]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1112]
	ldr r4, [r12, #300]
	ldr r5, [r12, #924]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1116]
	ldr r10, [r12, #1120]
	ldr r4, [r12, #928]
	and r4, r4, #1
	orr r4, r4, #2
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #856]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #860]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #864]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #868]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #872]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #876]
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

vg_ec_p192_decompress_public_key:
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
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #808]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #812]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #816]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #820]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #824]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #828]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #832]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #836]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #840]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #844]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #848]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #852]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #856]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #860]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #864]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #868]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #872]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #876]
	movw r10, #:lower16:({VG_P192_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P192_FRAME_CONSTS}
2:
	add r10, pc
3:
	mov r11, #51
20:
	sub r11, r11, #1
	add r5, r10, r11, lsl #3
	ldr r4, [r5, #0]
	ldr r5, [r5, #4]
	add r9, r12, r11, lsl #3
	str r4, [r9, #64]
	str r5, [r9, #68]
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1120]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1000]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1004]
	movw r4, #2
	movt r4, #0
	str r4, [r12, #1008]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1012]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1016]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1020]
	movw r4, #15000
	movt r4, #42723
	str r4, [r12, #1024]
	movw r4, #58374
	movt r4, #25305
	str r4, [r12, #1028]
	movw r4, #27362
	movt r4, #6407
	str r4, [r12, #1032]
	movw r4, #52658
	movt r4, #29313
	str r4, [r12, #1036]
	movw r4, #45361
	movt r4, #22464
	str r4, [r12, #1040]
	movw r4, #61125
	movt r4, #29640
	str r4, [r12, #1044]
	add r6, r1, #1
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #856]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #860]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #864]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #868]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #872]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #876]
	ldrb r4, [r1, #0]
	str r4, [r12, #832]
	orr r4, r4, #1
	eor r4, r4, #3
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #856]
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
	ldr r7, [r12, #860]
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
	ldr r7, [r12, #864]
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
	ldr r7, [r12, #868]
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
	ldr r7, [r12, #872]
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
	ldr r7, [r12, #876]
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
	sub r5, r3, #1
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	mov r10, lr
	mov r0, r12
	movw r1, #880
	movw r2, #856
	movw r3, #1000
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #880
	movw r3, #880
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1072
	movw r2, #1048
	movw r3, #880
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #208
	movw r3, #880
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #976
	movw r2, #1072
	movw r3, #1048
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1072
	movw r2, #976
	movw r3, #1024
	bl {vg_p192_add_mod_p}
	mov lr, r10
	movw r4, #0
	movt r4, #0
	str r4, [r12, #352]
	movw r4, #0
	movt r4, #49152
	str r4, [r12, #356]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #360]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #364]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #368]
	movw r4, #65535
	movt r4, #16383
	str r4, [r12, #372]
	mov r11, #24
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #352]
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
	bne 21b
	ldr r4, [r12, #184]
	str r4, [r12, #760]
	ldr r4, [r12, #188]
	str r4, [r12, #764]
	ldr r4, [r12, #192]
	str r4, [r12, #768]
	ldr r4, [r12, #196]
	str r4, [r12, #772]
	ldr r4, [r12, #200]
	str r4, [r12, #776]
	ldr r4, [r12, #204]
	str r4, [r12, #780]
	mov r11, #192
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #760
	movw r2, #760
	movw r3, #760
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #760
	movw r3, #1072
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #384]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #760]
	ldr r5, [r12, #784]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #760]
	ldr r4, [r12, #764]
	ldr r5, [r12, #788]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #764]
	ldr r4, [r12, #768]
	ldr r5, [r12, #792]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #768]
	ldr r4, [r12, #772]
	ldr r5, [r12, #796]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #772]
	ldr r4, [r12, #776]
	ldr r5, [r12, #800]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #776]
	ldr r4, [r12, #780]
	ldr r5, [r12, #804]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #780]
	cmp r11, #0
	bne 22b
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #760
	movw r3, #160
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #952
	movw r2, #136
	movw r3, #928
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	ldr r4, [r12, #928]
	ldr r5, [r12, #832]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	ldr r4, [r12, #928]
	ldr r5, [r12, #952]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #928]
	ldr r4, [r12, #932]
	ldr r5, [r12, #956]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #932]
	ldr r4, [r12, #936]
	ldr r5, [r12, #960]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #936]
	ldr r4, [r12, #940]
	ldr r5, [r12, #964]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #940]
	ldr r4, [r12, #944]
	ldr r5, [r12, #968]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #944]
	ldr r4, [r12, #948]
	ldr r5, [r12, #972]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #948]
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #928
	movw r3, #1000
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #904
	movw r3, #904
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #976
	movw r2, #1048
	movw r3, #1072
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #976]
	ldr r4, [r12, #980]
	orr r5, r5, r4
	ldr r4, [r12, #984]
	orr r5, r5, r4
	ldr r4, [r12, #988]
	orr r5, r5, r4
	ldr r4, [r12, #992]
	orr r5, r5, r4
	ldr r4, [r12, #996]
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
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	ldr r4, [r12, #928]
	ldr r5, [r12, #832]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	add r5, r10, #1
	mov r4, #0
	sub r5, r4, r5
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	ldr r10, [r12, #1120]
	mov r4, #4
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #856]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #860]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #864]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #868]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #872]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #876]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
	ldr r4, [r12, #928]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #932]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
	ldr r4, [r12, #936]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #940]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #944]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #948]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
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

vg_ec_p192_compress_public_key_umaal:
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
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #808]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #812]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #816]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #820]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #824]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #828]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #832]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #836]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #840]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #844]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #848]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #852]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #856]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #860]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #864]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #868]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #872]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #876]
	movw r10, #:lower16:({VG_P192_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P192_FRAME_CONSTS}
2:
	add r10, pc
3:
	mov r11, #51
20:
	sub r11, r11, #1
	add r5, r10, r11, lsl #3
	ldr r4, [r5, #0]
	ldr r5, [r5, #4]
	add r9, r12, r11, lsl #3
	str r4, [r9, #64]
	str r5, [r9, #68]
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1120]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1000]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1004]
	movw r4, #2
	movt r4, #0
	str r4, [r12, #1008]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1012]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1016]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1020]
	movw r4, #15000
	movt r4, #42723
	str r4, [r12, #1024]
	movw r4, #58374
	movt r4, #25305
	str r4, [r12, #1028]
	movw r4, #27362
	movt r4, #6407
	str r4, [r12, #1032]
	movw r4, #52658
	movt r4, #29313
	str r4, [r12, #1036]
	movw r4, #45361
	movt r4, #22464
	str r4, [r12, #1040]
	movw r4, #61125
	movt r4, #29640
	str r4, [r12, #1044]
	add r6, r1, #1
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #856]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #860]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #864]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #868]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #872]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #876]
	add r6, r6, #24
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #928]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #932]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #936]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #940]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #944]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #948]
	ldrb r4, [r1, #0]
	eor r4, r4, #4
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #856]
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
	ldr r7, [r12, #860]
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
	ldr r7, [r12, #864]
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
	ldr r7, [r12, #868]
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
	ldr r7, [r12, #872]
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
	ldr r7, [r12, #876]
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
	sub r5, r3, #1
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #928]
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
	ldr r7, [r12, #932]
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
	ldr r7, [r12, #936]
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
	ldr r7, [r12, #940]
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
	ldr r7, [r12, #944]
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
	ldr r7, [r12, #948]
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
	sub r5, r3, #1
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	mov r10, lr
	mov r0, r12
	movw r1, #880
	movw r2, #856
	movw r3, #1000
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #928
	movw r3, #1000
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #952
	movw r2, #904
	movw r3, #904
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #880
	movw r3, #880
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1072
	movw r2, #1048
	movw r3, #880
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #208
	movw r3, #880
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #976
	movw r2, #1072
	movw r3, #1048
	bl {vg_p192_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1072
	movw r2, #976
	movw r3, #1024
	bl {vg_p192_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #952
	movw r3, #1072
	bl {vg_p192_sub_mod_p_umaal}
	mov lr, r10
	ldr r5, [r12, #1048]
	ldr r4, [r12, #1052]
	orr r5, r5, r4
	ldr r4, [r12, #1056]
	orr r5, r5, r4
	ldr r4, [r12, #1060]
	orr r5, r5, r4
	ldr r4, [r12, #1064]
	orr r5, r5, r4
	ldr r4, [r12, #1068]
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
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	ldr r10, [r12, #1120]
	ldr r4, [r12, #256]
	ldr r5, [r12, #880]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #976]
	ldr r4, [r12, #260]
	ldr r5, [r12, #884]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #980]
	ldr r4, [r12, #264]
	ldr r5, [r12, #888]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #984]
	ldr r4, [r12, #268]
	ldr r5, [r12, #892]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #988]
	ldr r4, [r12, #272]
	ldr r5, [r12, #896]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #992]
	ldr r4, [r12, #276]
	ldr r5, [r12, #900]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #996]
	ldr r4, [r12, #280]
	ldr r5, [r12, #904]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1096]
	ldr r4, [r12, #284]
	ldr r5, [r12, #908]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1100]
	ldr r4, [r12, #288]
	ldr r5, [r12, #912]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1104]
	ldr r4, [r12, #292]
	ldr r5, [r12, #916]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1108]
	ldr r4, [r12, #296]
	ldr r5, [r12, #920]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1112]
	ldr r4, [r12, #300]
	ldr r5, [r12, #924]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1116]
	ldr r10, [r12, #1120]
	ldr r4, [r12, #928]
	and r4, r4, #1
	orr r4, r4, #2
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #856]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #860]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #864]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #868]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #872]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #876]
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

vg_ec_p192_decompress_public_key_umaal:
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
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #808]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #812]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #816]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #820]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #824]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #828]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #832]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #836]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #840]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #844]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #848]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #852]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #856]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #860]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #864]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #868]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #872]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #876]
	movw r10, #:lower16:({VG_P192_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P192_FRAME_CONSTS}
2:
	add r10, pc
3:
	mov r11, #51
20:
	sub r11, r11, #1
	add r5, r10, r11, lsl #3
	ldr r4, [r5, #0]
	ldr r5, [r5, #4]
	add r9, r12, r11, lsl #3
	str r4, [r9, #64]
	str r5, [r9, #68]
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1120]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1000]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1004]
	movw r4, #2
	movt r4, #0
	str r4, [r12, #1008]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1012]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1016]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1020]
	movw r4, #15000
	movt r4, #42723
	str r4, [r12, #1024]
	movw r4, #58374
	movt r4, #25305
	str r4, [r12, #1028]
	movw r4, #27362
	movt r4, #6407
	str r4, [r12, #1032]
	movw r4, #52658
	movt r4, #29313
	str r4, [r12, #1036]
	movw r4, #45361
	movt r4, #22464
	str r4, [r12, #1040]
	movw r4, #61125
	movt r4, #29640
	str r4, [r12, #1044]
	add r6, r1, #1
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #856]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #860]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #864]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #868]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #872]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #876]
	ldrb r4, [r1, #0]
	str r4, [r12, #832]
	orr r4, r4, #1
	eor r4, r4, #3
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #856]
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
	ldr r7, [r12, #860]
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
	ldr r7, [r12, #864]
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
	ldr r7, [r12, #868]
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
	ldr r7, [r12, #872]
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
	ldr r7, [r12, #876]
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
	sub r5, r3, #1
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	mov r10, lr
	mov r0, r12
	movw r1, #880
	movw r2, #856
	movw r3, #1000
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #880
	movw r3, #880
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1072
	movw r2, #1048
	movw r3, #880
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #208
	movw r3, #880
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #976
	movw r2, #1072
	movw r3, #1048
	bl {vg_p192_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1072
	movw r2, #976
	movw r3, #1024
	bl {vg_p192_add_mod_p_umaal}
	mov lr, r10
	movw r4, #0
	movt r4, #0
	str r4, [r12, #352]
	movw r4, #0
	movt r4, #49152
	str r4, [r12, #356]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #360]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #364]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #368]
	movw r4, #65535
	movt r4, #16383
	str r4, [r12, #372]
	mov r11, #24
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #352]
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
	bne 21b
	ldr r4, [r12, #184]
	str r4, [r12, #760]
	ldr r4, [r12, #188]
	str r4, [r12, #764]
	ldr r4, [r12, #192]
	str r4, [r12, #768]
	ldr r4, [r12, #196]
	str r4, [r12, #772]
	ldr r4, [r12, #200]
	str r4, [r12, #776]
	ldr r4, [r12, #204]
	str r4, [r12, #780]
	mov r11, #192
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #760
	movw r2, #760
	movw r3, #760
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #760
	movw r3, #1072
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #384]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #760]
	ldr r5, [r12, #784]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #760]
	ldr r4, [r12, #764]
	ldr r5, [r12, #788]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #764]
	ldr r4, [r12, #768]
	ldr r5, [r12, #792]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #768]
	ldr r4, [r12, #772]
	ldr r5, [r12, #796]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #772]
	ldr r4, [r12, #776]
	ldr r5, [r12, #800]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #776]
	ldr r4, [r12, #780]
	ldr r5, [r12, #804]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #780]
	cmp r11, #0
	bne 22b
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #760
	movw r3, #160
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #952
	movw r2, #136
	movw r3, #928
	bl {vg_p192_sub_mod_p_umaal}
	mov lr, r10
	ldr r4, [r12, #928]
	ldr r5, [r12, #832]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	ldr r4, [r12, #928]
	ldr r5, [r12, #952]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #928]
	ldr r4, [r12, #932]
	ldr r5, [r12, #956]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #932]
	ldr r4, [r12, #936]
	ldr r5, [r12, #960]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #936]
	ldr r4, [r12, #940]
	ldr r5, [r12, #964]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #940]
	ldr r4, [r12, #944]
	ldr r5, [r12, #968]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #944]
	ldr r4, [r12, #948]
	ldr r5, [r12, #972]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #948]
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #928
	movw r3, #1000
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #904
	movw r3, #904
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #976
	movw r2, #1048
	movw r3, #1072
	bl {vg_p192_sub_mod_p_umaal}
	mov lr, r10
	ldr r5, [r12, #976]
	ldr r4, [r12, #980]
	orr r5, r5, r4
	ldr r4, [r12, #984]
	orr r5, r5, r4
	ldr r4, [r12, #988]
	orr r5, r5, r4
	ldr r4, [r12, #992]
	orr r5, r5, r4
	ldr r4, [r12, #996]
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
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	ldr r4, [r12, #928]
	ldr r5, [r12, #832]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	add r5, r10, #1
	mov r4, #0
	sub r5, r4, r5
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	ldr r10, [r12, #1120]
	mov r4, #4
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #856]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #860]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #864]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #868]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #872]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #876]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
	ldr r4, [r12, #928]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #932]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
	ldr r4, [r12, #936]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #940]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #944]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #948]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
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
