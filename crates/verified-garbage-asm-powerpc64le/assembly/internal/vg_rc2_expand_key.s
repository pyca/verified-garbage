// The functions of `src/internal/vg_rc2_expand_key.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_expand_key:
	std %r14, 256(%r7)
	std %r15, 264(%r7)
	lis %r12, -4683
	ori %r12, %r12, 56601
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 50425
	ori %r12, %r12, 30937
	std %r12, 0(%r7)
	lis %r12, -25128
	ori %r12, %r12, 41034
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 31229
	ori %r12, %r12, 59688
	std %r12, 8(%r7)
	lis %r12, -29101
	ori %r12, %r12, 30251
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 33591
	ori %r12, %r12, 32454
	std %r12, 16(%r7)
	lis %r12, -23813
	ori %r12, %r12, 35652
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 34916
	ori %r12, %r12, 19554
	std %r12, 24(%r7)
	lis %r12, 4943
	ori %r12, %r12, 45959
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 62809
	ori %r12, %r12, 39447
	std %r12, 32(%r7)
	lis %r12, 12925
	ori %r12, %r12, 33033
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 36205
	ori %r12, %r12, 17761
	std %r12, 40(%r7)
	lis %r12, 2939
	ori %r12, %r12, 46982
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 60224
	ori %r12, %r12, 36797
	std %r12, 48(%r7)
	lis %r12, -32178
	ori %r12, %r12, 27484
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8737
	ori %r12, %r12, 38384
	std %r12, 56(%r7)
	lis %r12, 7346
	ori %r12, %r12, 24782
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 37733
	ori %r12, %r12, 54868
	std %r12, 64(%r7)
	lis %r12, -8975
	ori %r12, %r12, 36007
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5312
	ori %r12, %r12, 22131
	std %r12, 72(%r7)
	lis %r12, -11804
	ori %r12, %r12, 48699
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8138
	ori %r12, %r12, 29970
	std %r12, 80(%r7)
	lis %r12, 9910
	ori %r12, %r12, 15523
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 12500
	ori %r12, %r12, 15682
	std %r12, 88(%r7)
	lis %r12, 22279
	ori %r12, %r12, 26950
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 55822
	ori %r12, %r12, 49007
	std %r12, 96(%r7)
	lis %r12, 835
	ori %r12, %r12, 38076
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39709
	ori %r12, %r12, 61991
	std %r12, 104(%r7)
	lis %r12, -6338
	ori %r12, %r12, 61328
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 63175
	ori %r12, %r12, 4600
	std %r12, 112(%r7)
	lis %r12, -10466
	ori %r12, %r12, 26312
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 12245
	ori %r12, %r12, 49926
	std %r12, 120(%r7)
	lis %r12, -2066
	ori %r12, %r12, 21120
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 57066
	ori %r12, %r12, 59400
	std %r12, 128(%r7)
	lis %r12, 10858
	ori %r12, %r12, 19765
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 44146
	ori %r12, %r12, 43652
	std %r12, 136(%r7)
	lis %r12, 29769
	ori %r12, %r12, 5466
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 29138
	ori %r12, %r12, 6806
	std %r12, 144(%r7)
	lis %r12, -4956
	ori %r12, %r12, 6148
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24272
	ori %r12, %r12, 40779
	std %r12, 152(%r7)
	lis %r12, -13109
	ori %r12, %r12, 20751
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 28225
	ori %r12, %r12, 57538
	std %r12, 160(%r7)
	lis %r12, 14704
	ori %r12, %r12, 62625
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 20655
	ori %r12, %r12, 37156
	std %r12, 168(%r7)
	lis %r12, 31412
	ori %r12, %r12, 47139
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 34106
	ori %r12, %r12, 31897
	std %r12, 176(%r7)
	lis %r12, 12695
	ori %r12, %r12, 21797
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 23350
	ori %r12, %r12, 764
	std %r12, 184(%r7)
	lis %r12, -20846
	ori %r12, %r12, 35555
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39162
	ori %r12, %r12, 23853
	std %r12, 192(%r7)
	lis %r12, -13894
	ori %r12, %r12, 27751
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4137
	ori %r12, %r12, 57093
	std %r12, 200(%r7)
	lis %r12, 11432
	ori %r12, %r12, 40673
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 53222
	ori %r12, %r12, 211
	std %r12, 208(%r7)
	lis %r12, -22135
	ori %r12, %r12, 57944
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 16129
	ori %r12, %r12, 5731
	std %r12, 216(%r7)
	lis %r12, -20225
	ori %r12, %r12, 13227
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 6964
	ori %r12, %r12, 14349
	std %r12, 224(%r7)
	lis %r12, 11981
	ori %r12, %r12, 45497
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24332
	ori %r12, %r12, 18619
	std %r12, 232(%r7)
	lis %r12, 30620
	ori %r12, %r12, 42469
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 18395
	ori %r12, %r12, 62405
	std %r12, 240(%r7)
	lis %r12, -21055
	ori %r12, %r12, 32766
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 26656
	ori %r12, %r12, 42506
	std %r12, 248(%r7)
	li %r8, 0
20:
	add %r9, %r3, %r8
	lbz %r12, 0(%r9)
	add %r9, %r6, %r8
	stb %r12, 0(%r9)
	addi %r8, %r8, 1
	subf %r0, %r4, %r8
	cmpldi %cr0, %r0, 0
	bne %cr0, 20b
	li %r0, 128
	subf %r0, %r0, %r8
	cmpldi %cr0, %r0, 0
	beq %cr0, 21f
23:
	add %r9, %r6, %r8
	addi %r9, %r9, -1
	lbz %r10, 0(%r9)
	subf %r9, %r4, %r8
	add %r9, %r6, %r9
	lbz %r11, 0(%r9)
	add %r10, %r10, %r11
	rldicr %r10, %r10, 56, 7
	rldicl %r10, %r10, 8, 56
	li %r11, 0
	addi %r15, %r7, 248
24:
	subf %r0, %r7, %r15
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r15)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r7, %r15
	addi %r15, %r15, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 24b
	rldicr %r12, %r10, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 56, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 56, 7
	rldicl %r11, %r11, 8, 56
	add %r9, %r6, %r8
	stb %r11, 0(%r9)
	addi %r8, %r8, 1
	li %r0, 128
	subf %r0, %r0, %r8
	cmpldi %cr0, %r0, 0
	bne %cr0, 23b
	b 22f
21:
22:
	addi %r14, %r5, 7
	rldicl %r14, %r14, 61, 3
	li %r8, 128
	subf %r8, %r14, %r8
	rldicr %r9, %r5, 61, 2
	rldicl %r9, %r9, 3, 61
	li %r12, 255
	addi %r10, %r9, -1
	cmpldi %cr0, %r10, 0
	beq %cr0, 25f
	b 26f
25:
	li %r12, 1
26:
	addi %r10, %r9, -2
	cmpldi %cr0, %r10, 0
	beq %cr0, 27f
	b 28f
27:
	li %r12, 3
28:
	addi %r10, %r9, -3
	cmpldi %cr0, %r10, 0
	beq %cr0, 29f
	b 210f
29:
	li %r12, 7
210:
	addi %r10, %r9, -4
	cmpldi %cr0, %r10, 0
	beq %cr0, 211f
	b 212f
211:
	li %r12, 15
212:
	addi %r10, %r9, -5
	cmpldi %cr0, %r10, 0
	beq %cr0, 213f
	b 214f
213:
	li %r12, 31
214:
	addi %r10, %r9, -6
	cmpldi %cr0, %r10, 0
	beq %cr0, 215f
	b 216f
215:
	li %r12, 63
216:
	addi %r10, %r9, -7
	cmpldi %cr0, %r10, 0
	beq %cr0, 217f
	b 218f
217:
	li %r12, 127
218:
	add %r9, %r6, %r8
	lbz %r10, 0(%r9)
	and %r10, %r10, %r12
	li %r11, 0
	addi %r15, %r7, 248
219:
	subf %r0, %r7, %r15
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r15)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r7, %r15
	addi %r15, %r15, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 219b
	rldicr %r12, %r10, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 56, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 56, 7
	rldicl %r11, %r11, 8, 56
	add %r9, %r6, %r8
	stb %r11, 0(%r9)
	cmpldi %cr0, %r8, 0
	beq %cr0, 220f
222:
	addi %r8, %r8, -1
	add %r9, %r6, %r8
	lbz %r10, 1(%r9)
	add %r9, %r8, %r14
	add %r9, %r6, %r9
	lbz %r11, 0(%r9)
	xor %r10, %r10, %r11
	li %r11, 0
	addi %r15, %r7, 248
223:
	subf %r0, %r7, %r15
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r15)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r7, %r15
	addi %r15, %r15, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 223b
	rldicr %r12, %r10, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 56, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 56, 7
	rldicl %r11, %r11, 8, 56
	add %r9, %r6, %r8
	stb %r11, 0(%r9)
	cmpldi %cr0, %r8, 0
	bne %cr0, 222b
	b 221f
220:
221:
	ld %r14, 256(%r7)
	ld %r15, 264(%r7)
	blr
