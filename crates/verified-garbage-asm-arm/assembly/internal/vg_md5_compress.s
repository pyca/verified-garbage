// The functions of `src/internal/vg_md5_compress.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_compress:
	str r4, [r3, #0]
	str r5, [r3, #4]
	str r6, [r3, #8]
	str r7, [r3, #12]
	str r8, [r3, #16]
	str r9, [r3, #20]
	cmp r2, #0
	beq 20f
22:
	ldr r4, [r0, #0]
	ldr r5, [r0, #4]
	ldr r6, [r0, #8]
	ldr r7, [r0, #12]
	movw r8, #65535
	movt r8, #65535
	eor r12, r6, r7
	and r12, r12, r5
	eor r12, r12, r7
	add r4, r4, r12
	ldr r9, [r1, #0]
	add r4, r4, r9
	movw r9, #42104
	movt r9, #55146
	add r4, r4, r9
	add r4, r5, r4, ror #25
	eor r12, r5, r6
	and r12, r12, r4
	eor r12, r12, r6
	add r7, r7, r12
	ldr r9, [r1, #4]
	add r7, r7, r9
	movw r9, #46934
	movt r9, #59591
	add r7, r7, r9
	add r7, r4, r7, ror #20
	eor r12, r4, r5
	and r12, r12, r7
	eor r12, r12, r5
	add r6, r6, r12
	ldr r9, [r1, #8]
	add r6, r6, r9
	movw r9, #28891
	movt r9, #9248
	add r6, r6, r9
	add r6, r7, r6, ror #15
	eor r12, r7, r4
	and r12, r12, r6
	eor r12, r12, r4
	add r5, r5, r12
	ldr r9, [r1, #12]
	add r5, r5, r9
	movw r9, #52974
	movt r9, #49597
	add r5, r5, r9
	add r5, r6, r5, ror #10
	eor r12, r6, r7
	and r12, r12, r5
	eor r12, r12, r7
	add r4, r4, r12
	ldr r9, [r1, #16]
	add r4, r4, r9
	movw r9, #4015
	movt r9, #62844
	add r4, r4, r9
	add r4, r5, r4, ror #25
	eor r12, r5, r6
	and r12, r12, r4
	eor r12, r12, r6
	add r7, r7, r12
	ldr r9, [r1, #20]
	add r7, r7, r9
	movw r9, #50730
	movt r9, #18311
	add r7, r7, r9
	add r7, r4, r7, ror #20
	eor r12, r4, r5
	and r12, r12, r7
	eor r12, r12, r5
	add r6, r6, r12
	ldr r9, [r1, #24]
	add r6, r6, r9
	movw r9, #17939
	movt r9, #43056
	add r6, r6, r9
	add r6, r7, r6, ror #15
	eor r12, r7, r4
	and r12, r12, r6
	eor r12, r12, r4
	add r5, r5, r12
	ldr r9, [r1, #28]
	add r5, r5, r9
	movw r9, #38145
	movt r9, #64838
	add r5, r5, r9
	add r5, r6, r5, ror #10
	eor r12, r6, r7
	and r12, r12, r5
	eor r12, r12, r7
	add r4, r4, r12
	ldr r9, [r1, #32]
	add r4, r4, r9
	movw r9, #39128
	movt r9, #27008
	add r4, r4, r9
	add r4, r5, r4, ror #25
	eor r12, r5, r6
	and r12, r12, r4
	eor r12, r12, r6
	add r7, r7, r12
	ldr r9, [r1, #36]
	add r7, r7, r9
	movw r9, #63407
	movt r9, #35652
	add r7, r7, r9
	add r7, r4, r7, ror #20
	eor r12, r4, r5
	and r12, r12, r7
	eor r12, r12, r5
	add r6, r6, r12
	ldr r9, [r1, #40]
	add r6, r6, r9
	movw r9, #23473
	movt r9, #65535
	add r6, r6, r9
	add r6, r7, r6, ror #15
	eor r12, r7, r4
	and r12, r12, r6
	eor r12, r12, r4
	add r5, r5, r12
	ldr r9, [r1, #44]
	add r5, r5, r9
	movw r9, #55230
	movt r9, #35164
	add r5, r5, r9
	add r5, r6, r5, ror #10
	eor r12, r6, r7
	and r12, r12, r5
	eor r12, r12, r7
	add r4, r4, r12
	ldr r9, [r1, #48]
	add r4, r4, r9
	movw r9, #4386
	movt r9, #27536
	add r4, r4, r9
	add r4, r5, r4, ror #25
	eor r12, r5, r6
	and r12, r12, r4
	eor r12, r12, r6
	add r7, r7, r12
	ldr r9, [r1, #52]
	add r7, r7, r9
	movw r9, #29075
	movt r9, #64920
	add r7, r7, r9
	add r7, r4, r7, ror #20
	eor r12, r4, r5
	and r12, r12, r7
	eor r12, r12, r5
	add r6, r6, r12
	ldr r9, [r1, #56]
	add r6, r6, r9
	movw r9, #17294
	movt r9, #42617
	add r6, r6, r9
	add r6, r7, r6, ror #15
	eor r12, r7, r4
	and r12, r12, r6
	eor r12, r12, r4
	add r5, r5, r12
	ldr r9, [r1, #60]
	add r5, r5, r9
	movw r9, #2081
	movt r9, #18868
	add r5, r5, r9
	add r5, r6, r5, ror #10
	eor r12, r5, r6
	and r12, r12, r7
	eor r12, r12, r6
	add r4, r4, r12
	ldr r9, [r1, #4]
	add r4, r4, r9
	movw r9, #9570
	movt r9, #63006
	add r4, r4, r9
	add r4, r5, r4, ror #27
	eor r12, r4, r5
	and r12, r12, r6
	eor r12, r12, r5
	add r7, r7, r12
	ldr r9, [r1, #24]
	add r7, r7, r9
	movw r9, #45888
	movt r9, #49216
	add r7, r7, r9
	add r7, r4, r7, ror #23
	eor r12, r7, r4
	and r12, r12, r5
	eor r12, r12, r4
	add r6, r6, r12
	ldr r9, [r1, #44]
	add r6, r6, r9
	movw r9, #23121
	movt r9, #9822
	add r6, r6, r9
	add r6, r7, r6, ror #18
	eor r12, r6, r7
	and r12, r12, r4
	eor r12, r12, r7
	add r5, r5, r12
	ldr r9, [r1, #0]
	add r5, r5, r9
	movw r9, #51114
	movt r9, #59830
	add r5, r5, r9
	add r5, r6, r5, ror #12
	eor r12, r5, r6
	and r12, r12, r7
	eor r12, r12, r6
	add r4, r4, r12
	ldr r9, [r1, #20]
	add r4, r4, r9
	movw r9, #4189
	movt r9, #54831
	add r4, r4, r9
	add r4, r5, r4, ror #27
	eor r12, r4, r5
	and r12, r12, r6
	eor r12, r12, r5
	add r7, r7, r12
	ldr r9, [r1, #40]
	add r7, r7, r9
	movw r9, #5203
	movt r9, #580
	add r7, r7, r9
	add r7, r4, r7, ror #23
	eor r12, r7, r4
	and r12, r12, r5
	eor r12, r12, r4
	add r6, r6, r12
	ldr r9, [r1, #60]
	add r6, r6, r9
	movw r9, #59009
	movt r9, #55457
	add r6, r6, r9
	add r6, r7, r6, ror #18
	eor r12, r6, r7
	and r12, r12, r4
	eor r12, r12, r7
	add r5, r5, r12
	ldr r9, [r1, #16]
	add r5, r5, r9
	movw r9, #64456
	movt r9, #59347
	add r5, r5, r9
	add r5, r6, r5, ror #12
	eor r12, r5, r6
	and r12, r12, r7
	eor r12, r12, r6
	add r4, r4, r12
	ldr r9, [r1, #36]
	add r4, r4, r9
	movw r9, #52710
	movt r9, #8673
	add r4, r4, r9
	add r4, r5, r4, ror #27
	eor r12, r4, r5
	and r12, r12, r6
	eor r12, r12, r5
	add r7, r7, r12
	ldr r9, [r1, #56]
	add r7, r7, r9
	movw r9, #2006
	movt r9, #49975
	add r7, r7, r9
	add r7, r4, r7, ror #23
	eor r12, r7, r4
	and r12, r12, r5
	eor r12, r12, r4
	add r6, r6, r12
	ldr r9, [r1, #12]
	add r6, r6, r9
	movw r9, #3463
	movt r9, #62677
	add r6, r6, r9
	add r6, r7, r6, ror #18
	eor r12, r6, r7
	and r12, r12, r4
	eor r12, r12, r7
	add r5, r5, r12
	ldr r9, [r1, #32]
	add r5, r5, r9
	movw r9, #5357
	movt r9, #17754
	add r5, r5, r9
	add r5, r6, r5, ror #12
	eor r12, r5, r6
	and r12, r12, r7
	eor r12, r12, r6
	add r4, r4, r12
	ldr r9, [r1, #52]
	add r4, r4, r9
	movw r9, #59653
	movt r9, #43491
	add r4, r4, r9
	add r4, r5, r4, ror #27
	eor r12, r4, r5
	and r12, r12, r6
	eor r12, r12, r5
	add r7, r7, r12
	ldr r9, [r1, #8]
	add r7, r7, r9
	movw r9, #41976
	movt r9, #64751
	add r7, r7, r9
	add r7, r4, r7, ror #23
	eor r12, r7, r4
	and r12, r12, r5
	eor r12, r12, r4
	add r6, r6, r12
	ldr r9, [r1, #28]
	add r6, r6, r9
	movw r9, #729
	movt r9, #26479
	add r6, r6, r9
	add r6, r7, r6, ror #18
	eor r12, r6, r7
	and r12, r12, r4
	eor r12, r12, r7
	add r5, r5, r12
	ldr r9, [r1, #48]
	add r5, r5, r9
	movw r9, #19594
	movt r9, #36138
	add r5, r5, r9
	add r5, r6, r5, ror #12
	eor r12, r5, r6
	eor r12, r12, r7
	add r4, r4, r12
	ldr r9, [r1, #20]
	add r4, r4, r9
	movw r9, #14658
	movt r9, #65530
	add r4, r4, r9
	add r4, r5, r4, ror #28
	eor r12, r4, r5
	eor r12, r12, r6
	add r7, r7, r12
	ldr r9, [r1, #32]
	add r7, r7, r9
	movw r9, #63105
	movt r9, #34673
	add r7, r7, r9
	add r7, r4, r7, ror #21
	eor r12, r7, r4
	eor r12, r12, r5
	add r6, r6, r12
	ldr r9, [r1, #44]
	add r6, r6, r9
	movw r9, #24866
	movt r9, #28061
	add r6, r6, r9
	add r6, r7, r6, ror #16
	eor r12, r6, r7
	eor r12, r12, r4
	add r5, r5, r12
	ldr r9, [r1, #56]
	add r5, r5, r9
	movw r9, #14348
	movt r9, #64997
	add r5, r5, r9
	add r5, r6, r5, ror #9
	eor r12, r5, r6
	eor r12, r12, r7
	add r4, r4, r12
	ldr r9, [r1, #4]
	add r4, r4, r9
	movw r9, #59972
	movt r9, #42174
	add r4, r4, r9
	add r4, r5, r4, ror #28
	eor r12, r4, r5
	eor r12, r12, r6
	add r7, r7, r12
	ldr r9, [r1, #16]
	add r7, r7, r9
	movw r9, #53161
	movt r9, #19422
	add r7, r7, r9
	add r7, r4, r7, ror #21
	eor r12, r7, r4
	eor r12, r12, r5
	add r6, r6, r12
	ldr r9, [r1, #28]
	add r6, r6, r9
	movw r9, #19296
	movt r9, #63163
	add r6, r6, r9
	add r6, r7, r6, ror #16
	eor r12, r6, r7
	eor r12, r12, r4
	add r5, r5, r12
	ldr r9, [r1, #40]
	add r5, r5, r9
	movw r9, #48240
	movt r9, #48831
	add r5, r5, r9
	add r5, r6, r5, ror #9
	eor r12, r5, r6
	eor r12, r12, r7
	add r4, r4, r12
	ldr r9, [r1, #52]
	add r4, r4, r9
	movw r9, #32454
	movt r9, #10395
	add r4, r4, r9
	add r4, r5, r4, ror #28
	eor r12, r4, r5
	eor r12, r12, r6
	add r7, r7, r12
	ldr r9, [r1, #0]
	add r7, r7, r9
	movw r9, #10234
	movt r9, #60065
	add r7, r7, r9
	add r7, r4, r7, ror #21
	eor r12, r7, r4
	eor r12, r12, r5
	add r6, r6, r12
	ldr r9, [r1, #12]
	add r6, r6, r9
	movw r9, #12421
	movt r9, #54511
	add r6, r6, r9
	add r6, r7, r6, ror #16
	eor r12, r6, r7
	eor r12, r12, r4
	add r5, r5, r12
	ldr r9, [r1, #24]
	add r5, r5, r9
	movw r9, #7429
	movt r9, #1160
	add r5, r5, r9
	add r5, r6, r5, ror #9
	eor r12, r5, r6
	eor r12, r12, r7
	add r4, r4, r12
	ldr r9, [r1, #36]
	add r4, r4, r9
	movw r9, #53305
	movt r9, #55764
	add r4, r4, r9
	add r4, r5, r4, ror #28
	eor r12, r4, r5
	eor r12, r12, r6
	add r7, r7, r12
	ldr r9, [r1, #48]
	add r7, r7, r9
	movw r9, #39397
	movt r9, #59099
	add r7, r7, r9
	add r7, r4, r7, ror #21
	eor r12, r7, r4
	eor r12, r12, r5
	add r6, r6, r12
	ldr r9, [r1, #60]
	add r6, r6, r9
	movw r9, #31992
	movt r9, #8098
	add r6, r6, r9
	add r6, r7, r6, ror #16
	eor r12, r6, r7
	eor r12, r12, r4
	add r5, r5, r12
	ldr r9, [r1, #8]
	add r5, r5, r9
	movw r9, #22117
	movt r9, #50348
	add r5, r5, r9
	add r5, r6, r5, ror #9
	eor r12, r7, r8
	orr r12, r12, r5
	eor r12, r12, r6
	add r4, r4, r12
	ldr r9, [r1, #0]
	add r4, r4, r9
	movw r9, #8772
	movt r9, #62505
	add r4, r4, r9
	add r4, r5, r4, ror #26
	eor r12, r6, r8
	orr r12, r12, r4
	eor r12, r12, r5
	add r7, r7, r12
	ldr r9, [r1, #28]
	add r7, r7, r9
	movw r9, #65431
	movt r9, #17194
	add r7, r7, r9
	add r7, r4, r7, ror #22
	eor r12, r5, r8
	orr r12, r12, r7
	eor r12, r12, r4
	add r6, r6, r12
	ldr r9, [r1, #56]
	add r6, r6, r9
	movw r9, #9127
	movt r9, #43924
	add r6, r6, r9
	add r6, r7, r6, ror #17
	eor r12, r4, r8
	orr r12, r12, r6
	eor r12, r12, r7
	add r5, r5, r12
	ldr r9, [r1, #20]
	add r5, r5, r9
	movw r9, #41017
	movt r9, #64659
	add r5, r5, r9
	add r5, r6, r5, ror #11
	eor r12, r7, r8
	orr r12, r12, r5
	eor r12, r12, r6
	add r4, r4, r12
	ldr r9, [r1, #48]
	add r4, r4, r9
	movw r9, #22979
	movt r9, #25947
	add r4, r4, r9
	add r4, r5, r4, ror #26
	eor r12, r6, r8
	orr r12, r12, r4
	eor r12, r12, r5
	add r7, r7, r12
	ldr r9, [r1, #12]
	add r7, r7, r9
	movw r9, #52370
	movt r9, #36620
	add r7, r7, r9
	add r7, r4, r7, ror #22
	eor r12, r5, r8
	orr r12, r12, r7
	eor r12, r12, r4
	add r6, r6, r12
	ldr r9, [r1, #40]
	add r6, r6, r9
	movw r9, #62589
	movt r9, #65519
	add r6, r6, r9
	add r6, r7, r6, ror #17
	eor r12, r4, r8
	orr r12, r12, r6
	eor r12, r12, r7
	add r5, r5, r12
	ldr r9, [r1, #4]
	add r5, r5, r9
	movw r9, #24017
	movt r9, #34180
	add r5, r5, r9
	add r5, r6, r5, ror #11
	eor r12, r7, r8
	orr r12, r12, r5
	eor r12, r12, r6
	add r4, r4, r12
	ldr r9, [r1, #32]
	add r4, r4, r9
	movw r9, #32335
	movt r9, #28584
	add r4, r4, r9
	add r4, r5, r4, ror #26
	eor r12, r6, r8
	orr r12, r12, r4
	eor r12, r12, r5
	add r7, r7, r12
	ldr r9, [r1, #60]
	add r7, r7, r9
	movw r9, #59104
	movt r9, #65068
	add r7, r7, r9
	add r7, r4, r7, ror #22
	eor r12, r5, r8
	orr r12, r12, r7
	eor r12, r12, r4
	add r6, r6, r12
	ldr r9, [r1, #24]
	add r6, r6, r9
	movw r9, #17172
	movt r9, #41729
	add r6, r6, r9
	add r6, r7, r6, ror #17
	eor r12, r4, r8
	orr r12, r12, r6
	eor r12, r12, r7
	add r5, r5, r12
	ldr r9, [r1, #52]
	add r5, r5, r9
	movw r9, #4513
	movt r9, #19976
	add r5, r5, r9
	add r5, r6, r5, ror #11
	eor r12, r7, r8
	orr r12, r12, r5
	eor r12, r12, r6
	add r4, r4, r12
	ldr r9, [r1, #16]
	add r4, r4, r9
	movw r9, #32386
	movt r9, #63315
	add r4, r4, r9
	add r4, r5, r4, ror #26
	eor r12, r6, r8
	orr r12, r12, r4
	eor r12, r12, r5
	add r7, r7, r12
	ldr r9, [r1, #44]
	add r7, r7, r9
	movw r9, #62005
	movt r9, #48442
	add r7, r7, r9
	add r7, r4, r7, ror #22
	eor r12, r5, r8
	orr r12, r12, r7
	eor r12, r12, r4
	add r6, r6, r12
	ldr r9, [r1, #8]
	add r6, r6, r9
	movw r9, #53947
	movt r9, #10967
	add r6, r6, r9
	add r6, r7, r6, ror #17
	eor r12, r4, r8
	orr r12, r12, r6
	eor r12, r12, r7
	add r5, r5, r12
	ldr r9, [r1, #36]
	add r5, r5, r9
	movw r9, #54161
	movt r9, #60294
	add r5, r5, r9
	add r5, r6, r5, ror #11
	ldr r12, [r0, #0]
	add r4, r4, r12
	str r4, [r0, #0]
	ldr r12, [r0, #4]
	add r5, r5, r12
	str r5, [r0, #4]
	ldr r12, [r0, #8]
	add r6, r6, r12
	str r6, [r0, #8]
	ldr r12, [r0, #12]
	add r7, r7, r12
	str r7, [r0, #12]
	add r1, r1, #64
	subs r2, r2, #1
	bne 22b
	b 21f
20:
21:
	ldr r4, [r3, #0]
	ldr r5, [r3, #4]
	ldr r6, [r3, #8]
	ldr r7, [r3, #12]
	ldr r8, [r3, #16]
	ldr r9, [r3, #20]
	bx lr
