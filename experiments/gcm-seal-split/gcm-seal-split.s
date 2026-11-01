.text
.abiversion 2
.globl seal_base
.type seal_base,@function
seal_base:
// addi %r12, %r1, 0
.long 0x39810000
// ld %r12, 104(%r12)
.long 0xe98c0068
// std %r18, 128(%r12)
.long 0xfa4c0080
// std %r19, 136(%r12)
.long 0xfa6c0088
// std %r20, 144(%r12)
.long 0xfa8c0090
// std %r21, 152(%r12)
.long 0xfaac0098
// std %r22, 160(%r12)
.long 0xfacc00a0
// std %r23, 168(%r12)
.long 0xfaec00a8
// std %r24, 176(%r12)
.long 0xfb0c00b0
// std %r25, 184(%r12)
.long 0xfb2c00b8
// std %r26, 192(%r12)
.long 0xfb4c00c0
// std %r27, 200(%r12)
.long 0xfb6c00c8
// std %r28, 208(%r12)
.long 0xfb8c00d0
// std %r29, 216(%r12)
.long 0xfbac00d8
// std %r30, 224(%r12)
.long 0xfbcc00e0
// std %r31, 232(%r12)
.long 0xfbec00e8
// mflr %r0
.long 0x7c0802a6
// std %r0, 240(%r12)
.long 0xf80c00f0
// or %r31, %r12, %r12
.long 0x7d9f6378
// or %r29, %r3, %r3
.long 0x7c7d1b78
// or %r28, %r4, %r4
.long 0x7c9c2378
// addi %r30, %r31, 16
.long 0x3bdf0010
// or %r24, %r5, %r5
.long 0x7cb82b78
// or %r25, %r6, %r6
.long 0x7cd93378
// or %r18, %r6, %r6
.long 0x7cd23378
// or %r21, %r7, %r7
.long 0x7cf53b78
// or %r22, %r8, %r8
.long 0x7d164378
// or %r27, %r9, %r9
.long 0x7d3b4b78
// or %r23, %r10, %r10
.long 0x7d575378
// addi %r12, %r1, 0
.long 0x39810000
// ld %r20, 96(%r12)
.long 0xea8c0060
// addi %r6, %r25, -12
.long 0x38d9fff4
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 20f
// li %r0, 0
.long 0x38000000
// std %r0, 0(%r30)
.long 0xf81e0000
// std %r0, 8(%r30)
.long 0xf81e0008
// li %r26, 0
.long 0x3b400000
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 22f
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 24f
// li %r5, 16
.long 0x38a00010
// subf %r5, %r26, %r5
.long 0x7cba2850
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 26f
// subf %r6, %r5, %r25
.long 0x7cc5c850
// rldicl %r6, %r6, 1, 63
.long 0x78c60fe0
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 28f
b 29f
28:
// or %r5, %r25, %r25
.long 0x7f25cb78
29:
b 27f
26:
27:
// addi %r4, %r30, 32
.long 0x389e0020
// add %r4, %r4, %r26
.long 0x7c84d214
// or %r3, %r24, %r24
.long 0x7f03c378
// add %r24, %r24, %r5
.long 0x7f182a14
// subf %r25, %r5, %r25
.long 0x7f25c850
// add %r26, %r26, %r5
.long 0x7f5a2a14
210:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 210b
// addi %r6, %r26, -16
.long 0x38dafff0
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 211f
b 212f
211:
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 0
.long 0x389e0000
// addi %r5, %r30, 32
.long 0x38be0020
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
212:
b 25f
24:
25:
// or %r5, %r24, %r24
.long 0x7f05c378
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// li %r0, 15
.long 0x3800000f
// and %r8, %r25, %r0
.long 0x7f280038
// subf %r9, %r8, %r25
.long 0x7d28c850
// add %r24, %r24, %r9
.long 0x7f184a14
// or %r25, %r8, %r8
.long 0x7d194378
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 213f
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 0
.long 0x389e0000
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 214f
213:
214:
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 215f
// or %r3, %r24, %r24
.long 0x7f03c378
// addi %r4, %r30, 32
.long 0x389e0020
// or %r5, %r25, %r25
.long 0x7f25cb78
217:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 217b
b 216f
215:
216:
b 23f
22:
23:
// li %r0, 15
.long 0x3800000f
// and %r26, %r18, %r0
.long 0x7e5a0038
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 218f
// li %r0, 0
.long 0x38000000
// std %r0, 96(%r31)
.long 0xf81f0060
// std %r0, 104(%r31)
.long 0xf81f0068
// addi %r3, %r30, 32
.long 0x387e0020
// addi %r4, %r31, 96
.long 0x389f0060
// or %r5, %r26, %r26
.long 0x7f45d378
220:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 220b
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 0
.long 0x389e0000
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 219f
218:
219:
// li %r24, 0
.long 0x3b000000
// or %r26, %r18, %r18
.long 0x7e5a9378
// rldicr %r3, %r24, 3, 60
.long 0x7b031f24
// rldicr %r4, %r26, 3, 60
.long 0x7b441f24
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 0
.long 0x38c00000
// stdbrx %r3, %r5, %r6
.long 0x7c653528
// li %r6, 8
.long 0x38c00008
// stdbrx %r4, %r5, %r6
.long 0x7c853528
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 0
.long 0x389e0000
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 21f
20:
// lwz %r3, 0(%r24)
.long 0x80780000
// lwz %r4, 4(%r24)
.long 0x80980004
// lwz %r5, 8(%r24)
.long 0x80b80008
// lis %r6, 256
.long 0x3cc00100
// stw %r3, 0(%r30)
.long 0x907e0000
// stw %r4, 4(%r30)
.long 0x909e0004
// stw %r5, 8(%r30)
.long 0x90be0008
// stw %r6, 12(%r30)
.long 0x90de000c
21:
// lwz %r3, 0(%r30)
.long 0x807e0000
// lwz %r4, 4(%r30)
.long 0x809e0004
// lwz %r5, 8(%r30)
.long 0x80be0008
// addi %r7, %r30, 12
.long 0x38fe000c
// li %r8, 0
.long 0x39000000
// lwbrx %r6, %r7, %r8
.long 0x7cc7442c
// addi %r6, %r6, 1
.long 0x38c60001
// stw %r3, 48(%r30)
.long 0x907e0030
// stw %r4, 52(%r30)
.long 0x909e0034
// stw %r5, 56(%r30)
.long 0x90be0038
// addi %r7, %r30, 60
.long 0x38fe003c
// stwbrx %r6, %r7, %r8
.long 0x7cc7452c
// std %r8, 16(%r30)
.long 0xf91e0010
// std %r8, 24(%r30)
.long 0xf91e0018
// or %r24, %r21, %r21
.long 0x7eb8ab78
// or %r25, %r22, %r22
.long 0x7ed9b378
// li %r26, 0
.long 0x3b400000
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 221f
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 223f
// li %r5, 16
.long 0x38a00010
// subf %r5, %r26, %r5
.long 0x7cba2850
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 225f
// subf %r6, %r5, %r25
.long 0x7cc5c850
// rldicl %r6, %r6, 1, 63
.long 0x78c60fe0
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 227f
b 228f
227:
// or %r5, %r25, %r25
.long 0x7f25cb78
228:
b 226f
225:
226:
// addi %r4, %r30, 32
.long 0x389e0020
// add %r4, %r4, %r26
.long 0x7c84d214
// or %r3, %r24, %r24
.long 0x7f03c378
// add %r24, %r24, %r5
.long 0x7f182a14
// subf %r25, %r5, %r25
.long 0x7f25c850
// add %r26, %r26, %r5
.long 0x7f5a2a14
229:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 229b
// addi %r6, %r26, -16
.long 0x38dafff0
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 230f
b 231f
230:
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r30, 32
.long 0x38be0020
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
231:
b 224f
223:
224:
// or %r5, %r24, %r24
.long 0x7f05c378
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// li %r0, 15
.long 0x3800000f
// and %r8, %r25, %r0
.long 0x7f280038
// subf %r9, %r8, %r25
.long 0x7d28c850
// add %r24, %r24, %r9
.long 0x7f184a14
// or %r25, %r8, %r8
.long 0x7d194378
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 232f
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 233f
232:
233:
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 234f
// or %r3, %r24, %r24
.long 0x7f03c378
// addi %r4, %r30, 32
.long 0x389e0020
// or %r5, %r25, %r25
.long 0x7f25cb78
236:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 236b
b 235f
234:
235:
b 222f
221:
222:
// li %r0, 15
.long 0x3800000f
// and %r26, %r22, %r0
.long 0x7eda0038
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 237f
// li %r0, 0
.long 0x38000000
// std %r0, 96(%r31)
.long 0xf81f0060
// std %r0, 104(%r31)
.long 0xf81f0068
// addi %r3, %r30, 32
.long 0x387e0020
// addi %r4, %r31, 96
.long 0x389f0060
// or %r5, %r26, %r26
.long 0x7f45d378
239:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 239b
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 238f
237:
238:
// rldicl %r12, %r23, 55, 9
.long 0x7aecba42
// cmpldi %cr0, %r12, 0
.long 0x282c0000
beq %cr0, 240f
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// addi %r5, %r30, 48
.long 0x38be0030
// addi %r6, %r30, 16
.long 0x38de0010
// or %r7, %r27, %r27
.long 0x7f67db78
// rldicl %r8, %r23, 60, 4
.long 0x7ae8e102
// addi %r9, %r31, 448
.long 0x393f01c0
bl vg_aes_gcm_encrypt_blocks
// li %r0, 15
.long 0x3800000f
// and %r25, %r23, %r0
.long 0x7ef90038
// subf %r12, %r25, %r23
.long 0x7d99b850
// add %r24, %r27, %r12
.long 0x7f1b6214
// li %r26, 0
.long 0x3b400000
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 242f
// li %r0, 0
.long 0x38000000
// std %r0, 64(%r30)
.long 0xf81e0040
// std %r0, 72(%r30)
.long 0xf81e0048
// addi %r6, %r30, 64
.long 0x38de0040
// li %r7, 1
.long 0x38e00001
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// addi %r5, %r30, 48
.long 0x38be0030
// addi %r8, %r31, 512
.long 0x391f0200
bl vg_aes_ctr32
// addi %r3, %r30, 64
.long 0x387e0040
// or %r4, %r24, %r24
.long 0x7f04c378
// or %r5, %r25, %r25
.long 0x7f25cb78
244:
// lbz %r0, 0(%r4)
.long 0x88040000
// lbz %r6, 0(%r3)
.long 0x88c30000
// xor %r0, %r0, %r6
.long 0x7c003278
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 244b
b 243f
242:
243:
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 245f
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 247f
// li %r5, 16
.long 0x38a00010
// subf %r5, %r26, %r5
.long 0x7cba2850
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 249f
// subf %r6, %r5, %r25
.long 0x7cc5c850
// rldicl %r6, %r6, 1, 63
.long 0x78c60fe0
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 251f
b 252f
251:
// or %r5, %r25, %r25
.long 0x7f25cb78
252:
b 250f
249:
250:
// addi %r4, %r30, 32
.long 0x389e0020
// add %r4, %r4, %r26
.long 0x7c84d214
// or %r3, %r24, %r24
.long 0x7f03c378
// add %r24, %r24, %r5
.long 0x7f182a14
// subf %r25, %r5, %r25
.long 0x7f25c850
// add %r26, %r26, %r5
.long 0x7f5a2a14
253:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 253b
// addi %r6, %r26, -16
.long 0x38dafff0
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 254f
b 255f
254:
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r30, 32
.long 0x38be0020
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
255:
b 248f
247:
248:
// or %r5, %r24, %r24
.long 0x7f05c378
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// li %r0, 15
.long 0x3800000f
// and %r8, %r25, %r0
.long 0x7f280038
// subf %r9, %r8, %r25
.long 0x7d28c850
// add %r24, %r24, %r9
.long 0x7f184a14
// or %r25, %r8, %r8
.long 0x7d194378
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 256f
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 257f
256:
257:
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 258f
// or %r3, %r24, %r24
.long 0x7f03c378
// addi %r4, %r30, 32
.long 0x389e0020
// or %r5, %r25, %r25
.long 0x7f25cb78
260:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 260b
b 259f
258:
259:
b 246f
245:
246:
// cmpldi %cr0, %r23, 0
.long 0x28370000
beq %cr0, 261f
// li %r0, 15
.long 0x3800000f
// and %r26, %r23, %r0
.long 0x7efa0038
b 262f
261:
// li %r0, 15
.long 0x3800000f
// and %r26, %r22, %r0
.long 0x7eda0038
262:
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 263f
// li %r0, 0
.long 0x38000000
// std %r0, 96(%r31)
.long 0xf81f0060
// std %r0, 104(%r31)
.long 0xf81f0068
// addi %r3, %r30, 32
.long 0x387e0020
// addi %r4, %r31, 96
.long 0x389f0060
// or %r5, %r26, %r26
.long 0x7f45d378
265:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 265b
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 264f
263:
264:
// or %r24, %r22, %r22
.long 0x7ed8b378
// or %r26, %r23, %r23
.long 0x7efabb78
// rldicr %r3, %r24, 3, 60
.long 0x7b031f24
// rldicr %r4, %r26, 3, 60
.long 0x7b441f24
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 0
.long 0x38c00000
// stdbrx %r3, %r5, %r6
.long 0x7c653528
// li %r6, 8
.long 0x38c00008
// stdbrx %r4, %r5, %r6
.long 0x7c853528
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
// ld %r3, 16(%r30)
.long 0xe87e0010
// std %r3, 0(%r31)
.long 0xf87f0000
// ld %r3, 24(%r30)
.long 0xe87e0018
// std %r3, 8(%r31)
.long 0xf87f0008
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// or %r5, %r30, %r30
.long 0x7fc5f378
// addi %r6, %r31, 0
.long 0x38df0000
// li %r7, 1
.long 0x38e00001
// addi %r8, %r31, 512
.long 0x391f0200
bl vg_aes_ctr32
b 241f
240:
// or %r24, %r27, %r27
.long 0x7f78db78
// or %r25, %r23, %r23
.long 0x7ef9bb78
// li %r26, 0
.long 0x3b400000
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 266f
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 268f
// li %r5, 16
.long 0x38a00010
// subf %r5, %r26, %r5
.long 0x7cba2850
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 270f
// subf %r6, %r5, %r25
.long 0x7cc5c850
// rldicl %r6, %r6, 1, 63
.long 0x78c60fe0
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 272f
b 273f
272:
// or %r5, %r25, %r25
.long 0x7f25cb78
273:
b 271f
270:
271:
// addi %r3, %r30, 64
.long 0x387e0040
// add %r3, %r3, %r26
.long 0x7c63d214
// or %r4, %r24, %r24
.long 0x7f04c378
// add %r24, %r24, %r5
.long 0x7f182a14
// subf %r25, %r5, %r25
.long 0x7f25c850
274:
// lbz %r0, 0(%r4)
.long 0x88040000
// lbz %r6, 0(%r3)
.long 0x88c30000
// xor %r0, %r0, %r6
.long 0x7c003278
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 274b
b 269f
268:
269:
// or %r6, %r24, %r24
.long 0x7f06c378
// rldicl %r7, %r25, 60, 4
.long 0x7b27e102
// li %r0, 15
.long 0x3800000f
// and %r8, %r25, %r0
.long 0x7f280038
// subf %r9, %r8, %r25
.long 0x7d28c850
// add %r24, %r24, %r9
.long 0x7f184a14
// or %r25, %r8, %r8
.long 0x7d194378
// cmpldi %cr0, %r7, 0
.long 0x28270000
beq %cr0, 275f
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// addi %r5, %r30, 48
.long 0x38be0030
// addi %r8, %r31, 512
.long 0x391f0200
bl vg_aes_ctr32
b 276f
275:
276:
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 277f
// li %r0, 0
.long 0x38000000
// std %r0, 64(%r30)
.long 0xf81e0040
// std %r0, 72(%r30)
.long 0xf81e0048
// addi %r6, %r30, 64
.long 0x38de0040
// li %r7, 1
.long 0x38e00001
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// addi %r5, %r30, 48
.long 0x38be0030
// addi %r8, %r31, 512
.long 0x391f0200
bl vg_aes_ctr32
// addi %r3, %r30, 64
.long 0x387e0040
// or %r4, %r24, %r24
.long 0x7f04c378
// or %r5, %r25, %r25
.long 0x7f25cb78
279:
// lbz %r0, 0(%r4)
.long 0x88040000
// lbz %r6, 0(%r3)
.long 0x88c30000
// xor %r0, %r0, %r6
.long 0x7c003278
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 279b
b 278f
277:
278:
b 267f
266:
267:
// or %r24, %r27, %r27
.long 0x7f78db78
// or %r25, %r23, %r23
.long 0x7ef9bb78
// li %r26, 0
.long 0x3b400000
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 280f
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 282f
// li %r5, 16
.long 0x38a00010
// subf %r5, %r26, %r5
.long 0x7cba2850
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 284f
// subf %r6, %r5, %r25
.long 0x7cc5c850
// rldicl %r6, %r6, 1, 63
.long 0x78c60fe0
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 286f
b 287f
286:
// or %r5, %r25, %r25
.long 0x7f25cb78
287:
b 285f
284:
285:
// addi %r4, %r30, 32
.long 0x389e0020
// add %r4, %r4, %r26
.long 0x7c84d214
// or %r3, %r24, %r24
.long 0x7f03c378
// add %r24, %r24, %r5
.long 0x7f182a14
// subf %r25, %r5, %r25
.long 0x7f25c850
// add %r26, %r26, %r5
.long 0x7f5a2a14
288:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 288b
// addi %r6, %r26, -16
.long 0x38dafff0
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 289f
b 290f
289:
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r30, 32
.long 0x38be0020
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
290:
b 283f
282:
283:
// or %r5, %r24, %r24
.long 0x7f05c378
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// li %r0, 15
.long 0x3800000f
// and %r8, %r25, %r0
.long 0x7f280038
// subf %r9, %r8, %r25
.long 0x7d28c850
// add %r24, %r24, %r9
.long 0x7f184a14
// or %r25, %r8, %r8
.long 0x7d194378
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 291f
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 292f
291:
292:
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 293f
// or %r3, %r24, %r24
.long 0x7f03c378
// addi %r4, %r30, 32
.long 0x389e0020
// or %r5, %r25, %r25
.long 0x7f25cb78
295:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 295b
b 294f
293:
294:
b 281f
280:
281:
// li %r0, 15
.long 0x3800000f
// and %r26, %r23, %r0
.long 0x7efa0038
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 296f
// li %r0, 0
.long 0x38000000
// std %r0, 96(%r31)
.long 0xf81f0060
// std %r0, 104(%r31)
.long 0xf81f0068
// addi %r3, %r30, 32
.long 0x387e0020
// addi %r4, %r31, 96
.long 0x389f0060
// or %r5, %r26, %r26
.long 0x7f45d378
298:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 298b
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 297f
296:
297:
// or %r24, %r22, %r22
.long 0x7ed8b378
// or %r26, %r23, %r23
.long 0x7efabb78
// rldicr %r3, %r24, 3, 60
.long 0x7b031f24
// rldicr %r4, %r26, 3, 60
.long 0x7b441f24
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 0
.long 0x38c00000
// stdbrx %r3, %r5, %r6
.long 0x7c653528
// li %r6, 8
.long 0x38c00008
// stdbrx %r4, %r5, %r6
.long 0x7c853528
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
// ld %r3, 16(%r30)
.long 0xe87e0010
// std %r3, 0(%r31)
.long 0xf87f0000
// ld %r3, 24(%r30)
.long 0xe87e0018
// std %r3, 8(%r31)
.long 0xf87f0008
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// or %r5, %r30, %r30
.long 0x7fc5f378
// addi %r6, %r31, 0
.long 0x38df0000
// li %r7, 1
.long 0x38e00001
// addi %r8, %r31, 512
.long 0x391f0200
bl vg_aes_ctr32
241:
// ld %r3, 0(%r31)
.long 0xe87f0000
// std %r3, 0(%r20)
.long 0xf8740000
// ld %r3, 8(%r31)
.long 0xe87f0008
// std %r3, 8(%r20)
.long 0xf8740008
// or %r12, %r31, %r31
.long 0x7fecfb78
// ld %r0, 240(%r12)
.long 0xe80c00f0
// mtlr %r0
.long 0x7c0803a6
// ld %r18, 128(%r12)
.long 0xea4c0080
// ld %r19, 136(%r12)
.long 0xea6c0088
// ld %r20, 144(%r12)
.long 0xea8c0090
// ld %r21, 152(%r12)
.long 0xeaac0098
// ld %r22, 160(%r12)
.long 0xeacc00a0
// ld %r23, 168(%r12)
.long 0xeaec00a8
// ld %r24, 176(%r12)
.long 0xeb0c00b0
// ld %r25, 184(%r12)
.long 0xeb2c00b8
// ld %r26, 192(%r12)
.long 0xeb4c00c0
// ld %r27, 200(%r12)
.long 0xeb6c00c8
// ld %r28, 208(%r12)
.long 0xeb8c00d0
// ld %r29, 216(%r12)
.long 0xebac00d8
// ld %r30, 224(%r12)
.long 0xebcc00e0
// ld %r31, 232(%r12)
.long 0xebec00e8
// blr
.long 0x4e800020
.globl seal_split_probe
.type seal_split_probe,@function
seal_split_probe:
// addi %r12, %r1, 0
.long 0x39810000
// ld %r12, 104(%r12)
.long 0xe98c0068
// std %r18, 128(%r12)
.long 0xfa4c0080
// std %r19, 136(%r12)
.long 0xfa6c0088
// std %r20, 144(%r12)
.long 0xfa8c0090
// std %r21, 152(%r12)
.long 0xfaac0098
// std %r22, 160(%r12)
.long 0xfacc00a0
// std %r23, 168(%r12)
.long 0xfaec00a8
// std %r24, 176(%r12)
.long 0xfb0c00b0
// std %r25, 184(%r12)
.long 0xfb2c00b8
// std %r26, 192(%r12)
.long 0xfb4c00c0
// std %r27, 200(%r12)
.long 0xfb6c00c8
// std %r28, 208(%r12)
.long 0xfb8c00d0
// std %r29, 216(%r12)
.long 0xfbac00d8
// std %r30, 224(%r12)
.long 0xfbcc00e0
// std %r31, 232(%r12)
.long 0xfbec00e8
// mflr %r0
.long 0x7c0802a6
// std %r0, 240(%r12)
.long 0xf80c00f0
// or %r31, %r12, %r12
.long 0x7d9f6378
// or %r29, %r3, %r3
.long 0x7c7d1b78
// or %r28, %r4, %r4
.long 0x7c9c2378
// addi %r30, %r31, 16
.long 0x3bdf0010
// or %r24, %r5, %r5
.long 0x7cb82b78
// or %r25, %r6, %r6
.long 0x7cd93378
// or %r18, %r6, %r6
.long 0x7cd23378
// or %r21, %r7, %r7
.long 0x7cf53b78
// or %r22, %r8, %r8
.long 0x7d164378
// or %r27, %r9, %r9
.long 0x7d3b4b78
// or %r23, %r10, %r10
.long 0x7d575378
// addi %r12, %r1, 0
.long 0x39810000
// ld %r20, 96(%r12)
.long 0xea8c0060
// addi %r6, %r25, -12
.long 0x38d9fff4
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 20f
// li %r0, 0
.long 0x38000000
// std %r0, 0(%r30)
.long 0xf81e0000
// std %r0, 8(%r30)
.long 0xf81e0008
// li %r26, 0
.long 0x3b400000
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 22f
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 24f
// li %r5, 16
.long 0x38a00010
// subf %r5, %r26, %r5
.long 0x7cba2850
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 26f
// subf %r6, %r5, %r25
.long 0x7cc5c850
// rldicl %r6, %r6, 1, 63
.long 0x78c60fe0
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 28f
b 29f
28:
// or %r5, %r25, %r25
.long 0x7f25cb78
29:
b 27f
26:
27:
// addi %r4, %r30, 32
.long 0x389e0020
// add %r4, %r4, %r26
.long 0x7c84d214
// or %r3, %r24, %r24
.long 0x7f03c378
// add %r24, %r24, %r5
.long 0x7f182a14
// subf %r25, %r5, %r25
.long 0x7f25c850
// add %r26, %r26, %r5
.long 0x7f5a2a14
210:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 210b
// addi %r6, %r26, -16
.long 0x38dafff0
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 211f
b 212f
211:
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 0
.long 0x389e0000
// addi %r5, %r30, 32
.long 0x38be0020
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
212:
b 25f
24:
25:
// or %r5, %r24, %r24
.long 0x7f05c378
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// li %r0, 15
.long 0x3800000f
// and %r8, %r25, %r0
.long 0x7f280038
// subf %r9, %r8, %r25
.long 0x7d28c850
// add %r24, %r24, %r9
.long 0x7f184a14
// or %r25, %r8, %r8
.long 0x7d194378
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 213f
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 0
.long 0x389e0000
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 214f
213:
214:
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 215f
// or %r3, %r24, %r24
.long 0x7f03c378
// addi %r4, %r30, 32
.long 0x389e0020
// or %r5, %r25, %r25
.long 0x7f25cb78
217:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 217b
b 216f
215:
216:
b 23f
22:
23:
// li %r0, 15
.long 0x3800000f
// and %r26, %r18, %r0
.long 0x7e5a0038
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 218f
// li %r0, 0
.long 0x38000000
// std %r0, 96(%r31)
.long 0xf81f0060
// std %r0, 104(%r31)
.long 0xf81f0068
// addi %r3, %r30, 32
.long 0x387e0020
// addi %r4, %r31, 96
.long 0x389f0060
// or %r5, %r26, %r26
.long 0x7f45d378
220:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 220b
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 0
.long 0x389e0000
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 219f
218:
219:
// li %r24, 0
.long 0x3b000000
// or %r26, %r18, %r18
.long 0x7e5a9378
// rldicr %r3, %r24, 3, 60
.long 0x7b031f24
// rldicr %r4, %r26, 3, 60
.long 0x7b441f24
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 0
.long 0x38c00000
// stdbrx %r3, %r5, %r6
.long 0x7c653528
// li %r6, 8
.long 0x38c00008
// stdbrx %r4, %r5, %r6
.long 0x7c853528
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 0
.long 0x389e0000
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 21f
20:
// lwz %r3, 0(%r24)
.long 0x80780000
// lwz %r4, 4(%r24)
.long 0x80980004
// lwz %r5, 8(%r24)
.long 0x80b80008
// lis %r6, 256
.long 0x3cc00100
// stw %r3, 0(%r30)
.long 0x907e0000
// stw %r4, 4(%r30)
.long 0x909e0004
// stw %r5, 8(%r30)
.long 0x90be0008
// stw %r6, 12(%r30)
.long 0x90de000c
21:
// lwz %r3, 0(%r30)
.long 0x807e0000
// lwz %r4, 4(%r30)
.long 0x809e0004
// lwz %r5, 8(%r30)
.long 0x80be0008
// addi %r7, %r30, 12
.long 0x38fe000c
// li %r8, 0
.long 0x39000000
// lwbrx %r6, %r7, %r8
.long 0x7cc7442c
// addi %r6, %r6, 1
.long 0x38c60001
// stw %r3, 48(%r30)
.long 0x907e0030
// stw %r4, 52(%r30)
.long 0x909e0034
// stw %r5, 56(%r30)
.long 0x90be0038
// addi %r7, %r30, 60
.long 0x38fe003c
// stwbrx %r6, %r7, %r8
.long 0x7cc7452c
// std %r8, 16(%r30)
.long 0xf91e0010
// std %r8, 24(%r30)
.long 0xf91e0018
// or %r24, %r21, %r21
.long 0x7eb8ab78
// or %r25, %r22, %r22
.long 0x7ed9b378
// li %r26, 0
.long 0x3b400000
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 221f
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 223f
// li %r5, 16
.long 0x38a00010
// subf %r5, %r26, %r5
.long 0x7cba2850
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 225f
// subf %r6, %r5, %r25
.long 0x7cc5c850
// rldicl %r6, %r6, 1, 63
.long 0x78c60fe0
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 227f
b 228f
227:
// or %r5, %r25, %r25
.long 0x7f25cb78
228:
b 226f
225:
226:
// addi %r4, %r30, 32
.long 0x389e0020
// add %r4, %r4, %r26
.long 0x7c84d214
// or %r3, %r24, %r24
.long 0x7f03c378
// add %r24, %r24, %r5
.long 0x7f182a14
// subf %r25, %r5, %r25
.long 0x7f25c850
// add %r26, %r26, %r5
.long 0x7f5a2a14
229:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 229b
// addi %r6, %r26, -16
.long 0x38dafff0
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 230f
b 231f
230:
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r30, 32
.long 0x38be0020
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
231:
b 224f
223:
224:
// or %r5, %r24, %r24
.long 0x7f05c378
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// li %r0, 15
.long 0x3800000f
// and %r8, %r25, %r0
.long 0x7f280038
// subf %r9, %r8, %r25
.long 0x7d28c850
// add %r24, %r24, %r9
.long 0x7f184a14
// or %r25, %r8, %r8
.long 0x7d194378
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 232f
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 233f
232:
233:
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 234f
// or %r3, %r24, %r24
.long 0x7f03c378
// addi %r4, %r30, 32
.long 0x389e0020
// or %r5, %r25, %r25
.long 0x7f25cb78
236:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 236b
b 235f
234:
235:
b 222f
221:
222:
// li %r0, 15
.long 0x3800000f
// and %r26, %r22, %r0
.long 0x7eda0038
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 237f
// li %r0, 0
.long 0x38000000
// std %r0, 96(%r31)
.long 0xf81f0060
// std %r0, 104(%r31)
.long 0xf81f0068
// addi %r3, %r30, 32
.long 0x387e0020
// addi %r4, %r31, 96
.long 0x389f0060
// or %r5, %r26, %r26
.long 0x7f45d378
239:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 239b
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 238f
237:
238:
// std %r17, 112(%r31)
.long 0xfa3f0070
// addi %r12, %r1, 0
.long 0x39810000
// ld %r17, 112(%r12)
.long 0xea2c0070
// ld %r19, 120(%r12)
.long 0xea6c0078
// rldicl %r12, %r23, 55, 9
.long 0x7aecba42
// cmpldi %cr0, %r12, 0
.long 0x282c0000
beq %cr0, 240f
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// addi %r5, %r30, 48
.long 0x38be0030
// addi %r6, %r30, 16
.long 0x38de0010
// or %r7, %r27, %r27
.long 0x7f67db78
// rldicl %r8, %r23, 60, 4
.long 0x7ae8e102
// addi %r9, %r31, 448
.long 0x393f01c0
bl vg_gcm_split_probe
// li %r0, 15
.long 0x3800000f
// and %r25, %r23, %r0
.long 0x7ef90038
// subf %r12, %r25, %r23
.long 0x7d99b850
// add %r24, %r27, %r12
.long 0x7f1b6214
// li %r26, 0
.long 0x3b400000
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 242f
// li %r0, 0
.long 0x38000000
// std %r0, 64(%r30)
.long 0xf81e0040
// std %r0, 72(%r30)
.long 0xf81e0048
// addi %r6, %r30, 64
.long 0x38de0040
// li %r7, 1
.long 0x38e00001
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// addi %r5, %r30, 48
.long 0x38be0030
// addi %r8, %r31, 512
.long 0x391f0200
bl vg_aes_ctr32
// addi %r3, %r30, 64
.long 0x387e0040
// or %r4, %r24, %r24
.long 0x7f04c378
// or %r5, %r25, %r25
.long 0x7f25cb78
244:
// lbz %r0, 0(%r4)
.long 0x88040000
// lbz %r6, 0(%r3)
.long 0x88c30000
// xor %r0, %r0, %r6
.long 0x7c003278
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 244b
b 243f
242:
243:
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 245f
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 247f
// li %r5, 16
.long 0x38a00010
// subf %r5, %r26, %r5
.long 0x7cba2850
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 249f
// subf %r6, %r5, %r25
.long 0x7cc5c850
// rldicl %r6, %r6, 1, 63
.long 0x78c60fe0
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 251f
b 252f
251:
// or %r5, %r25, %r25
.long 0x7f25cb78
252:
b 250f
249:
250:
// addi %r4, %r30, 32
.long 0x389e0020
// add %r4, %r4, %r26
.long 0x7c84d214
// or %r3, %r24, %r24
.long 0x7f03c378
// add %r24, %r24, %r5
.long 0x7f182a14
// subf %r25, %r5, %r25
.long 0x7f25c850
// add %r26, %r26, %r5
.long 0x7f5a2a14
253:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 253b
// addi %r6, %r26, -16
.long 0x38dafff0
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 254f
b 255f
254:
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r30, 32
.long 0x38be0020
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
255:
b 248f
247:
248:
// or %r5, %r24, %r24
.long 0x7f05c378
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// li %r0, 15
.long 0x3800000f
// and %r8, %r25, %r0
.long 0x7f280038
// subf %r9, %r8, %r25
.long 0x7d28c850
// add %r24, %r24, %r9
.long 0x7f184a14
// or %r25, %r8, %r8
.long 0x7d194378
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 256f
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 257f
256:
257:
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 258f
// or %r3, %r24, %r24
.long 0x7f03c378
// addi %r4, %r30, 32
.long 0x389e0020
// or %r5, %r25, %r25
.long 0x7f25cb78
260:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 260b
b 259f
258:
259:
b 246f
245:
246:
// cmpldi %cr0, %r23, 0
.long 0x28370000
beq %cr0, 261f
// li %r0, 15
.long 0x3800000f
// and %r26, %r23, %r0
.long 0x7efa0038
b 262f
261:
// li %r0, 15
.long 0x3800000f
// and %r26, %r22, %r0
.long 0x7eda0038
262:
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 263f
// li %r0, 0
.long 0x38000000
// std %r0, 96(%r31)
.long 0xf81f0060
// std %r0, 104(%r31)
.long 0xf81f0068
// addi %r3, %r30, 32
.long 0x387e0020
// addi %r4, %r31, 96
.long 0x389f0060
// or %r5, %r26, %r26
.long 0x7f45d378
265:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 265b
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 264f
263:
264:
// or %r24, %r22, %r22
.long 0x7ed8b378
// or %r26, %r23, %r23
.long 0x7efabb78
// rldicr %r3, %r24, 3, 60
.long 0x7b031f24
// rldicr %r4, %r26, 3, 60
.long 0x7b441f24
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 0
.long 0x38c00000
// stdbrx %r3, %r5, %r6
.long 0x7c653528
// li %r6, 8
.long 0x38c00008
// stdbrx %r4, %r5, %r6
.long 0x7c853528
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
// ld %r3, 16(%r30)
.long 0xe87e0010
// std %r3, 0(%r31)
.long 0xf87f0000
// ld %r3, 24(%r30)
.long 0xe87e0018
// std %r3, 8(%r31)
.long 0xf87f0008
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// or %r5, %r30, %r30
.long 0x7fc5f378
// addi %r6, %r31, 0
.long 0x38df0000
// li %r7, 1
.long 0x38e00001
// addi %r8, %r31, 512
.long 0x391f0200
bl vg_aes_ctr32
b 241f
240:
// or %r30, %r27, %r27
.long 0x7f7edb78
// cmpldi %cr0, %r19, 0
.long 0x28330000
beq %cr0, 266f
// or %r11, %r30, %r30
.long 0x7fcbf378
// li %r0, 0
.long 0x38000000
268:
// lxvd2x 49, %r17, %r0
.long 0x7e310699
// stxvd2x 49, %r11, %r0
.long 0x7e2b0799
// addi %r17, %r17, 16
.long 0x3a310010
// addi %r11, %r11, 16
.long 0x396b0010
// addi %r19, %r19, -1
.long 0x3a73ffff
// cmpldi %cr0, %r19, 0
.long 0x28330000
bne %cr0, 268b
b 267f
266:
267:
// addi %r30, %r31, 16
.long 0x3bdf0010
// or %r24, %r27, %r27
.long 0x7f78db78
// or %r25, %r23, %r23
.long 0x7ef9bb78
// li %r26, 0
.long 0x3b400000
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 269f
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 271f
// li %r5, 16
.long 0x38a00010
// subf %r5, %r26, %r5
.long 0x7cba2850
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 273f
// subf %r6, %r5, %r25
.long 0x7cc5c850
// rldicl %r6, %r6, 1, 63
.long 0x78c60fe0
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 275f
b 276f
275:
// or %r5, %r25, %r25
.long 0x7f25cb78
276:
b 274f
273:
274:
// addi %r3, %r30, 64
.long 0x387e0040
// add %r3, %r3, %r26
.long 0x7c63d214
// or %r4, %r24, %r24
.long 0x7f04c378
// add %r24, %r24, %r5
.long 0x7f182a14
// subf %r25, %r5, %r25
.long 0x7f25c850
277:
// lbz %r0, 0(%r4)
.long 0x88040000
// lbz %r6, 0(%r3)
.long 0x88c30000
// xor %r0, %r0, %r6
.long 0x7c003278
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 277b
b 272f
271:
272:
// or %r6, %r24, %r24
.long 0x7f06c378
// rldicl %r7, %r25, 60, 4
.long 0x7b27e102
// li %r0, 15
.long 0x3800000f
// and %r8, %r25, %r0
.long 0x7f280038
// subf %r9, %r8, %r25
.long 0x7d28c850
// add %r24, %r24, %r9
.long 0x7f184a14
// or %r25, %r8, %r8
.long 0x7d194378
// cmpldi %cr0, %r7, 0
.long 0x28270000
beq %cr0, 278f
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// addi %r5, %r30, 48
.long 0x38be0030
// addi %r8, %r31, 512
.long 0x391f0200
bl vg_aes_ctr32
b 279f
278:
279:
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 280f
// li %r0, 0
.long 0x38000000
// std %r0, 64(%r30)
.long 0xf81e0040
// std %r0, 72(%r30)
.long 0xf81e0048
// addi %r6, %r30, 64
.long 0x38de0040
// li %r7, 1
.long 0x38e00001
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// addi %r5, %r30, 48
.long 0x38be0030
// addi %r8, %r31, 512
.long 0x391f0200
bl vg_aes_ctr32
// addi %r3, %r30, 64
.long 0x387e0040
// or %r4, %r24, %r24
.long 0x7f04c378
// or %r5, %r25, %r25
.long 0x7f25cb78
282:
// lbz %r0, 0(%r4)
.long 0x88040000
// lbz %r6, 0(%r3)
.long 0x88c30000
// xor %r0, %r0, %r6
.long 0x7c003278
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 282b
b 281f
280:
281:
b 270f
269:
270:
// or %r24, %r27, %r27
.long 0x7f78db78
// or %r25, %r23, %r23
.long 0x7ef9bb78
// li %r26, 0
.long 0x3b400000
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 283f
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 285f
// li %r5, 16
.long 0x38a00010
// subf %r5, %r26, %r5
.long 0x7cba2850
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 287f
// subf %r6, %r5, %r25
.long 0x7cc5c850
// rldicl %r6, %r6, 1, 63
.long 0x78c60fe0
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 289f
b 290f
289:
// or %r5, %r25, %r25
.long 0x7f25cb78
290:
b 288f
287:
288:
// addi %r4, %r30, 32
.long 0x389e0020
// add %r4, %r4, %r26
.long 0x7c84d214
// or %r3, %r24, %r24
.long 0x7f03c378
// add %r24, %r24, %r5
.long 0x7f182a14
// subf %r25, %r5, %r25
.long 0x7f25c850
// add %r26, %r26, %r5
.long 0x7f5a2a14
291:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 291b
// addi %r6, %r26, -16
.long 0x38dafff0
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 292f
b 293f
292:
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r30, 32
.long 0x38be0020
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
293:
b 286f
285:
286:
// or %r5, %r24, %r24
.long 0x7f05c378
// rldicl %r6, %r25, 60, 4
.long 0x7b26e102
// li %r0, 15
.long 0x3800000f
// and %r8, %r25, %r0
.long 0x7f280038
// subf %r9, %r8, %r25
.long 0x7d28c850
// add %r24, %r24, %r9
.long 0x7f184a14
// or %r25, %r8, %r8
.long 0x7d194378
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 294f
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 295f
294:
295:
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 296f
// or %r3, %r24, %r24
.long 0x7f03c378
// addi %r4, %r30, 32
.long 0x389e0020
// or %r5, %r25, %r25
.long 0x7f25cb78
298:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 298b
b 297f
296:
297:
b 284f
283:
284:
// li %r0, 15
.long 0x3800000f
// and %r26, %r23, %r0
.long 0x7efa0038
// cmpldi %cr0, %r26, 0
.long 0x283a0000
beq %cr0, 299f
// li %r0, 0
.long 0x38000000
// std %r0, 96(%r31)
.long 0xf81f0060
// std %r0, 104(%r31)
.long 0xf81f0068
// addi %r3, %r30, 32
.long 0x387e0020
// addi %r4, %r31, 96
.long 0x389f0060
// or %r5, %r26, %r26
.long 0x7f45d378
2101:
// lbz %r0, 0(%r3)
.long 0x88030000
// stb %r0, 0(%r4)
.long 0x98040000
// addi %r3, %r3, 1
.long 0x38630001
// addi %r4, %r4, 1
.long 0x38840001
// addi %r5, %r5, -1
.long 0x38a5ffff
// cmpldi %cr0, %r5, 0
.long 0x28250000
bne %cr0, 2101b
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
b 2100f
299:
2100:
// or %r24, %r22, %r22
.long 0x7ed8b378
// or %r26, %r23, %r23
.long 0x7efabb78
// rldicr %r3, %r24, 3, 60
.long 0x7b031f24
// rldicr %r4, %r26, 3, 60
.long 0x7b441f24
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 0
.long 0x38c00000
// stdbrx %r3, %r5, %r6
.long 0x7c653528
// li %r6, 8
.long 0x38c00008
// stdbrx %r4, %r5, %r6
.long 0x7c853528
// addi %r3, %r29, 240
.long 0x387d00f0
// addi %r4, %r30, 16
.long 0x389e0010
// addi %r5, %r31, 96
.long 0x38bf0060
// li %r6, 1
.long 0x38c00001
// addi %r7, %r31, 512
.long 0x38ff0200
bl vg_ghash
// ld %r3, 16(%r30)
.long 0xe87e0010
// std %r3, 0(%r31)
.long 0xf87f0000
// ld %r3, 24(%r30)
.long 0xe87e0018
// std %r3, 8(%r31)
.long 0xf87f0008
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// or %r5, %r30, %r30
.long 0x7fc5f378
// addi %r6, %r31, 0
.long 0x38df0000
// li %r7, 1
.long 0x38e00001
// addi %r8, %r31, 512
.long 0x391f0200
bl vg_aes_ctr32
241:
// ld %r17, 112(%r31)
.long 0xea3f0070
// ld %r3, 0(%r31)
.long 0xe87f0000
// std %r3, 0(%r20)
.long 0xf8740000
// ld %r3, 8(%r31)
.long 0xe87f0008
// std %r3, 8(%r20)
.long 0xf8740008
// or %r12, %r31, %r31
.long 0x7fecfb78
// ld %r0, 240(%r12)
.long 0xe80c00f0
// mtlr %r0
.long 0x7c0803a6
// ld %r18, 128(%r12)
.long 0xea4c0080
// ld %r19, 136(%r12)
.long 0xea6c0088
// ld %r20, 144(%r12)
.long 0xea8c0090
// ld %r21, 152(%r12)
.long 0xeaac0098
// ld %r22, 160(%r12)
.long 0xeacc00a0
// ld %r23, 168(%r12)
.long 0xeaec00a8
// ld %r24, 176(%r12)
.long 0xeb0c00b0
// ld %r25, 184(%r12)
.long 0xeb2c00b8
// ld %r26, 192(%r12)
.long 0xeb4c00c0
// ld %r27, 200(%r12)
.long 0xeb6c00c8
// ld %r28, 208(%r12)
.long 0xeb8c00d0
// ld %r29, 216(%r12)
.long 0xebac00d8
// ld %r30, 224(%r12)
.long 0xebcc00e0
// ld %r31, 232(%r12)
.long 0xebec00e8
// blr
.long 0x4e800020
.globl vg_gcm_split_probe
.type vg_gcm_split_probe,@function
vg_gcm_split_probe:
// cmpldi %cr0, %r8, 0
.long 0x28280000
beq %cr0, 20f
// std %r25, 0(%r9)
.long 0xfb290000
// std %r26, 8(%r9)
.long 0xfb490008
// std %r27, 16(%r9)
.long 0xfb690010
// std %r28, 24(%r9)
.long 0xfb890018
// std %r29, 32(%r9)
.long 0xfba90020
// std %r30, 40(%r9)
.long 0xfbc90028
// std %r31, 48(%r9)
.long 0xfbe90030
// mflr %r0
.long 0x7c0802a6
// std %r0, 56(%r9)
.long 0xf8090038
// or %r29, %r3, %r3
.long 0x7c7d1b78
// or %r28, %r4, %r4
.long 0x7c9c2378
// or %r27, %r5, %r5
.long 0x7cbb2b78
// or %r26, %r6, %r6
.long 0x7cda3378
// or %r30, %r7, %r7
.long 0x7cfe3b78
// or %r25, %r8, %r8
.long 0x7d194378
// or %r31, %r9, %r9
.long 0x7d3f4b78
// rldicl %r12, %r25, 59, 5
.long 0x7b2cd942
// cmpldi %cr0, %r12, 0
.long 0x282c0000
beq %cr0, 22f
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// or %r5, %r27, %r27
.long 0x7f65db78
// or %r6, %r30, %r30
.long 0x7fc6f378
// li %r0, 7
.long 0x38000007
// and %r11, %r25, %r0
.long 0x7f2b0038
// subf %r7, %r11, %r25
.long 0x7cebc850
// addi %r8, %r29, 240
.long 0x391d00f0
// or %r9, %r26, %r26
.long 0x7f49d378
// addi %r10, %r31, 64
.long 0x395f0040
// cmpldi %cr0, %r7, 0
.long 0x28270000
beq %cr0, 24f
// std %r14, 0(%r10)
.long 0xf9ca0000
// std %r15, 8(%r10)
.long 0xf9ea0008
// std %r16, 16(%r10)
.long 0xfa0a0010
// std %r20, 40(%r10)
.long 0xfa8a0028
// std %r21, 48(%r10)
.long 0xfaaa0030
// std %r22, 56(%r10)
.long 0xfaca0038
// std %r23, 64(%r10)
.long 0xfaea0040
// std %r24, 72(%r10)
.long 0xfb0a0048
// std %r18, 80(%r10)
.long 0xfa4a0050
// or %r16, %r10, %r10
.long 0x7d505378
// addi %r16, %r16, 128
.long 0x3a100080
// or %r14, %r9, %r9
.long 0x7d2e4b78
// li %r15, 112
.long 0x39e00070
// li %r0, 0
.long 0x38000000
// vxor %v0, %v0, %v0
.long 0x100004c4
// lis %r11, 1798
.long 0x3d600706
// ori %r11, %r11, 1284
.long 0x616b0504
// rldicr %r11, %r11, 32, 31
.long 0x796b07c6
// oris %r11, %r11, 770
.long 0x656b0302
// ori %r11, %r11, 256
.long 0x616b0100
// lis %r12, 3854
.long 0x3d800f0e
// ori %r12, %r12, 3340
.long 0x618c0d0c
// rldicr %r12, %r12, 32, 31
.long 0x798c07c6
// oris %r12, %r12, 2826
.long 0x658c0b0a
// ori %r12, %r12, 2312
.long 0x618c0908
// mtvsrd 51, %r11
.long 0x7e6b0167
// mtvsrd 33, %r12
.long 0x7c2c0167
// vsldoi %v19, %v0, %v19, 8
.long 0x12609a2c
// vsldoi %v19, %v19, %v1, 8
.long 0x12730a2c
// li %r20, 16
.long 0x3a800010
// addi %r24, %r16, 256
.long 0x3b100100
// li %r18, 96
.long 0x3a400060
// lis %r11, 0
.long 0x3d600000
// ori %r11, %r11, 0
.long 0x616b0000
// rldicr %r11, %r11, 32, 31
.long 0x796b07c6
// oris %r11, %r11, 0
.long 0x656b0000
// ori %r11, %r11, 0
.long 0x616b0000
// lis %r12, 0
.long 0x3d800000
// ori %r12, %r12, 0
.long 0x618c0000
// rldicr %r12, %r12, 32, 31
.long 0x798c07c6
// oris %r12, %r12, 0
.long 0x658c0000
// ori %r12, %r12, 1
.long 0x618c0001
// mtvsrd 49, %r11
.long 0x7e2b0167
// mtvsrd 33, %r12
.long 0x7c2c0167
// vsldoi %v17, %v0, %v17, 8
.long 0x12208a2c
// vsldoi %v17, %v17, %v1, 8
.long 0x12310a2c
// stxvd2x 49, %r16, %r20
.long 0x7e30a799
// lis %r11, -15872
.long 0x3d60c200
// ori %r11, %r11, 0
.long 0x616b0000
// rldicr %r11, %r11, 32, 31
.long 0x796b07c6
// oris %r11, %r11, 0
.long 0x656b0000
// ori %r11, %r11, 0
.long 0x616b0000
// lis %r12, -15872
.long 0x3d80c200
// ori %r12, %r12, 0
.long 0x618c0000
// rldicr %r12, %r12, 32, 31
.long 0x798c07c6
// oris %r12, %r12, 0
.long 0x658c0000
// ori %r12, %r12, 0
.long 0x618c0000
// mtvsrd 45, %r11
.long 0x7dab0167
// mtvsrd 33, %r12
.long 0x7c2c0167
// vsldoi %v13, %v0, %v13, 8
.long 0x11a06a2c
// vsldoi %v13, %v13, %v1, 8
.long 0x11ad0a2c
// lis %r11, 17920
.long 0x3d604600
// ori %r11, %r11, 0
.long 0x616b0000
// rldicr %r11, %r11, 32, 31
.long 0x796b07c6
// oris %r11, %r11, 0
.long 0x656b0000
// ori %r11, %r11, 0
.long 0x616b0000
// lis %r12, 0
.long 0x3d800000
// ori %r12, %r12, 0
.long 0x618c0000
// rldicr %r12, %r12, 32, 31
.long 0x798c07c6
// oris %r12, %r12, 0
.long 0x658c0000
// ori %r12, %r12, 3
.long 0x618c0003
// mtvsrd 43, %r11
.long 0x7d6b0167
// mtvsrd 33, %r12
.long 0x7c2c0167
// vsldoi %v11, %v0, %v11, 8
.long 0x11605a2c
// vsldoi %v11, %v11, %v1, 8
.long 0x116b0a2c
// lxvd2x 41, %r8, %r0
.long 0x7d280699
// vperm %v9, %v9, %v9, %v19
.long 0x11294ceb
// vsldoi %v9, %v9, %v9, 8
.long 0x11294a2c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v11, %v16, %v18
.long 0x117094c4
// vsldoi %v11, %v11, %v11, 8
.long 0x116b5a2c
// lxvd2x 42, %r14, %r0
.long 0x7d4e0699
// vperm %v10, %v10, %v10, %v19
.long 0x114a54eb
// li %r11, 12
.long 0x3960000c
// lwbrx %r8, %r5, %r11
.long 0x7d055c2c
// or %r9, %r3, %r3
.long 0x7c691b78
// vor %v12, %v11, %v11
.long 0x118b5c84
// vor %v8, %v12, %v12
.long 0x110c6484
// vsldoi %v9, %v12, %v12, 8
.long 0x112c622c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v12, %v16, %v18
.long 0x119094c4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vsldoi %v9, %v8, %v8, 8
.long 0x1128422c
// vsldoi %v18, %v9, %v12, 8
.long 0x1249622c
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vsldoi %v8, %v12, %v9, 8
.long 0x110c4a2c
// li %r11, 224
.long 0x396000e0
// stxvd2x 40, %r16, %r11
.long 0x7d105f99
// li %r11, 240
.long 0x396000f0
// stxvd2x 50, %r16, %r11
.long 0x7e505f99
// vsldoi %v9, %v12, %v12, 8
.long 0x112c622c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v12, %v16, %v18
.long 0x119094c4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vor %v8, %v12, %v12
.long 0x110c6484
// vsldoi %v9, %v12, %v12, 8
.long 0x112c622c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v12, %v16, %v18
.long 0x119094c4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vsldoi %v9, %v8, %v8, 8
.long 0x1128422c
// vsldoi %v18, %v9, %v12, 8
.long 0x1249622c
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vsldoi %v8, %v12, %v9, 8
.long 0x110c4a2c
// li %r11, 192
.long 0x396000c0
// stxvd2x 40, %r16, %r11
.long 0x7d105f99
// li %r11, 208
.long 0x396000d0
// stxvd2x 50, %r16, %r11
.long 0x7e505f99
// vsldoi %v9, %v12, %v12, 8
.long 0x112c622c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v12, %v16, %v18
.long 0x119094c4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vor %v8, %v12, %v12
.long 0x110c6484
// vsldoi %v9, %v12, %v12, 8
.long 0x112c622c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v12, %v16, %v18
.long 0x119094c4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vsldoi %v9, %v8, %v8, 8
.long 0x1128422c
// vsldoi %v18, %v9, %v12, 8
.long 0x1249622c
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vsldoi %v8, %v12, %v9, 8
.long 0x110c4a2c
// li %r11, 160
.long 0x396000a0
// stxvd2x 40, %r16, %r11
.long 0x7d105f99
// li %r11, 176
.long 0x396000b0
// stxvd2x 50, %r16, %r11
.long 0x7e505f99
// vsldoi %v9, %v12, %v12, 8
.long 0x112c622c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v12, %v16, %v18
.long 0x119094c4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vor %v8, %v12, %v12
.long 0x110c6484
// vsldoi %v9, %v12, %v12, 8
.long 0x112c622c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v12, %v16, %v18
.long 0x119094c4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vsldoi %v9, %v8, %v8, 8
.long 0x1128422c
// vsldoi %v18, %v9, %v12, 8
.long 0x1249622c
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vsldoi %v8, %v12, %v9, 8
.long 0x110c4a2c
// li %r11, 128
.long 0x39600080
// stxvd2x 40, %r16, %r11
.long 0x7d105f99
// li %r11, 144
.long 0x39600090
// stxvd2x 50, %r16, %r11
.long 0x7e505f99
// lis %r11, 2057
.long 0x3d600809
// ori %r11, %r11, 2571
.long 0x616b0a0b
// rldicr %r11, %r11, 32, 31
.long 0x796b07c6
// oris %r11, %r11, 3085
.long 0x656b0c0d
// ori %r11, %r11, 3599
.long 0x616b0e0f
// lis %r12, 6169
.long 0x3d801819
// ori %r12, %r12, 6683
.long 0x618c1a1b
// rldicr %r12, %r12, 32, 31
.long 0x798c07c6
// oris %r12, %r12, 7197
.long 0x658c1c1d
// ori %r12, %r12, 7711
.long 0x618c1e1f
// mtvsrd 49, %r11
.long 0x7e2b0167
// mtvsrd 33, %r12
.long 0x7c2c0167
// vsldoi %v17, %v0, %v17, 8
.long 0x12208a2c
// vsldoi %v17, %v17, %v1, 8
.long 0x12310a2c
// li %r11, 32
.long 0x39600020
// stxvd2x 49, %r16, %r11
.long 0x7e305f99
// lis %r11, 1
.long 0x3d600001
// ori %r11, %r11, 515
.long 0x616b0203
// rldicr %r11, %r11, 32, 31
.long 0x796b07c6
// oris %r11, %r11, 1029
.long 0x656b0405
// ori %r11, %r11, 1543
.long 0x616b0607
// lis %r12, 4113
.long 0x3d801011
// ori %r12, %r12, 4627
.long 0x618c1213
// rldicr %r12, %r12, 32, 31
.long 0x798c07c6
// oris %r12, %r12, 5141
.long 0x658c1415
// ori %r12, %r12, 5655
.long 0x618c1617
// mtvsrd 49, %r11
.long 0x7e2b0167
// mtvsrd 33, %r12
.long 0x7c2c0167
// vsldoi %v17, %v0, %v17, 8
.long 0x12208a2c
// vsldoi %v17, %v17, %v1, 8
.long 0x12310a2c
// li %r11, 48
.long 0x39600030
// stxvd2x 49, %r16, %r11
.long 0x7e305f99
// li %r11, 80
.long 0x39600050
// stxvd2x 51, %r16, %r11
.long 0x7e705f99
// li %r11, 96
.long 0x39600060
// stxvd2x 45, %r16, %r11
.long 0x7db05f99
// or %r11, %r24, %r24
.long 0x7f0bc378
// addi %r12, %r4, 1
.long 0x39840001
26:
// lxvd2x 40, %r9, %r0
.long 0x7d090699
// vperm %v8, %v8, %v8, %v19
.long 0x110844eb
// stxvd2x 40, %r11, %r0
.long 0x7d0b0799
// addi %r9, %r9, 16
.long 0x39290010
// addi %r11, %r11, 16
.long 0x396b0010
// addi %r12, %r12, -1
.long 0x398cffff
// cmpldi %cr0, %r12, 0
.long 0x282c0000
bne %cr0, 26b
// or %r3, %r24, %r24
.long 0x7f03c378
// li %r23, 64
.long 0x3ae00040
// li %r24, 80
.long 0x3b000050
// lxvd2x 32, %r5, %r0
.long 0x7c050699
// vperm %v0, %v0, %v0, %v19
.long 0x100004eb
// stxvd2x 32, %r16, %r15
.long 0x7c107f99
27:
// lxvd2x 32, %r16, %r15
.long 0x7c107e99
// lxvd2x 49, %r16, %r20
.long 0x7e30a699
// vadduwm %v18, %v17, %v17
.long 0x12518880
// vadduwm %v1, %v0, %v17
.long 0x10208880
// vadduwm %v2, %v0, %v18
.long 0x10409080
// vadduwm %v3, %v1, %v18
.long 0x10619080
// vadduwm %v4, %v2, %v18
.long 0x10829080
// vadduwm %v5, %v3, %v18
.long 0x10a39080
// vadduwm %v6, %v4, %v18
.long 0x10c49080
// vadduwm %v7, %v5, %v18
.long 0x10e59080
// vadduwm %v18, %v6, %v18
.long 0x12469080
// stxvd2x 50, %r16, %r15
.long 0x7e507f99
// addi %r8, %r8, 8
.long 0x39080008
// lxvd2x 40, %r3, %r0
.long 0x7d030699
// vxor %v0, %v0, %v8
.long 0x100044c4
// vxor %v1, %v1, %v8
.long 0x102144c4
// vxor %v2, %v2, %v8
.long 0x104244c4
// vxor %v3, %v3, %v8
.long 0x106344c4
// vxor %v4, %v4, %v8
.long 0x108444c4
// vxor %v5, %v5, %v8
.long 0x10a544c4
// vxor %v6, %v6, %v8
.long 0x10c644c4
// vxor %v7, %v7, %v8
.long 0x10e744c4
// lxvd2x 40, %r3, %r20
.long 0x7d03a699
// li %r21, 32
.long 0x3aa00020
// lxvd2x 41, %r3, %r21
.long 0x7d23ae99
// li %r22, 48
.long 0x3ac00030
// lxvd2x 43, %r3, %r22
.long 0x7d63b699
// lxvd2x 44, %r3, %r23
.long 0x7d83be99
// lxvd2x 46, %r3, %r24
.long 0x7dc3c699
// lxvd2x 47, %r3, %r18
.long 0x7de39699
// li %r11, 112
.long 0x39600070
// lxvd2x 48, %r3, %r11
.long 0x7e035e99
// li %r12, 128
.long 0x39800080
// lxvd2x 49, %r3, %r12
.long 0x7e236699
// addi %r9, %r3, 144
.long 0x39230090
// lxvd2x 50, %r9, %r0
.long 0x7e490699
// vcipher %v0, %v0, %v8
.long 0x10004508
// vcipher %v1, %v1, %v8
.long 0x10214508
// vcipher %v2, %v2, %v8
.long 0x10424508
// vcipher %v3, %v3, %v8
.long 0x10634508
// vcipher %v4, %v4, %v8
.long 0x10844508
// vcipher %v5, %v5, %v8
.long 0x10a54508
// vcipher %v6, %v6, %v8
.long 0x10c64508
// vcipher %v7, %v7, %v8
.long 0x10e74508
// vcipher %v0, %v0, %v9
.long 0x10004d08
// vcipher %v1, %v1, %v9
.long 0x10214d08
// vcipher %v2, %v2, %v9
.long 0x10424d08
// vcipher %v3, %v3, %v9
.long 0x10634d08
// vcipher %v4, %v4, %v9
.long 0x10844d08
// vcipher %v5, %v5, %v9
.long 0x10a54d08
// vcipher %v6, %v6, %v9
.long 0x10c64d08
// vcipher %v7, %v7, %v9
.long 0x10e74d08
// rldicr %r12, %r4, 4, 59
.long 0x788c26e4
// lxvd2x 41, %r3, %r12
.long 0x7d236699
// vcipher %v0, %v0, %v11
.long 0x10005d08
// vcipher %v1, %v1, %v11
.long 0x10215d08
// vcipher %v2, %v2, %v11
.long 0x10425d08
// vcipher %v3, %v3, %v11
.long 0x10635d08
// vcipher %v4, %v4, %v11
.long 0x10845d08
// vcipher %v5, %v5, %v11
.long 0x10a55d08
// vcipher %v6, %v6, %v11
.long 0x10c65d08
// vcipher %v7, %v7, %v11
.long 0x10e75d08
// vcipher %v0, %v0, %v12
.long 0x10006508
// vcipher %v1, %v1, %v12
.long 0x10216508
// vcipher %v2, %v2, %v12
.long 0x10426508
// vcipher %v3, %v3, %v12
.long 0x10636508
// vcipher %v4, %v4, %v12
.long 0x10846508
// vcipher %v5, %v5, %v12
.long 0x10a56508
// vcipher %v6, %v6, %v12
.long 0x10c66508
// vcipher %v7, %v7, %v12
.long 0x10e76508
// vcipher %v0, %v0, %v14
.long 0x10007508
// vcipher %v1, %v1, %v14
.long 0x10217508
// vcipher %v2, %v2, %v14
.long 0x10427508
// vcipher %v3, %v3, %v14
.long 0x10637508
// vcipher %v4, %v4, %v14
.long 0x10847508
// vcipher %v5, %v5, %v14
.long 0x10a57508
// vcipher %v6, %v6, %v14
.long 0x10c67508
// vcipher %v7, %v7, %v14
.long 0x10e77508
// vcipher %v0, %v0, %v15
.long 0x10007d08
// vcipher %v1, %v1, %v15
.long 0x10217d08
// vcipher %v2, %v2, %v15
.long 0x10427d08
// vcipher %v3, %v3, %v15
.long 0x10637d08
// vcipher %v4, %v4, %v15
.long 0x10847d08
// vcipher %v5, %v5, %v15
.long 0x10a57d08
// vcipher %v6, %v6, %v15
.long 0x10c67d08
// vcipher %v7, %v7, %v15
.long 0x10e77d08
// vcipher %v0, %v0, %v16
.long 0x10008508
// vcipher %v1, %v1, %v16
.long 0x10218508
// vcipher %v2, %v2, %v16
.long 0x10428508
// vcipher %v3, %v3, %v16
.long 0x10638508
// vcipher %v4, %v4, %v16
.long 0x10848508
// vcipher %v5, %v5, %v16
.long 0x10a58508
// vcipher %v6, %v6, %v16
.long 0x10c68508
// vcipher %v7, %v7, %v16
.long 0x10e78508
// vcipher %v0, %v0, %v17
.long 0x10008d08
// vcipher %v1, %v1, %v17
.long 0x10218d08
// vcipher %v2, %v2, %v17
.long 0x10428d08
// vcipher %v3, %v3, %v17
.long 0x10638d08
// vcipher %v4, %v4, %v17
.long 0x10848d08
// vcipher %v5, %v5, %v17
.long 0x10a58d08
// vcipher %v6, %v6, %v17
.long 0x10c68d08
// vcipher %v7, %v7, %v17
.long 0x10e78d08
// vcipher %v0, %v0, %v18
.long 0x10009508
// vcipher %v1, %v1, %v18
.long 0x10219508
// vcipher %v2, %v2, %v18
.long 0x10429508
// vcipher %v3, %v3, %v18
.long 0x10639508
// vcipher %v4, %v4, %v18
.long 0x10849508
// vcipher %v5, %v5, %v18
.long 0x10a59508
// vcipher %v6, %v6, %v18
.long 0x10c69508
// vcipher %v7, %v7, %v18
.long 0x10e79508
// addi %r9, %r3, 160
.long 0x392300a0
// addi %r10, %r4, -10
.long 0x3944fff6
// cmpldi %cr0, %r10, 0
.long 0x282a0000
beq %cr0, 28f
210:
// lxvd2x 40, %r9, %r0
.long 0x7d090699
// vcipher %v0, %v0, %v8
.long 0x10004508
// vcipher %v1, %v1, %v8
.long 0x10214508
// vcipher %v2, %v2, %v8
.long 0x10424508
// vcipher %v3, %v3, %v8
.long 0x10634508
// vcipher %v4, %v4, %v8
.long 0x10844508
// vcipher %v5, %v5, %v8
.long 0x10a54508
// vcipher %v6, %v6, %v8
.long 0x10c64508
// vcipher %v7, %v7, %v8
.long 0x10e74508
// addi %r9, %r9, 16
.long 0x39290010
// addi %r10, %r10, -1
.long 0x394affff
// cmpldi %cr0, %r10, 0
.long 0x282a0000
bne %cr0, 210b
b 29f
28:
29:
// vcipherlast %v0, %v0, %v9
.long 0x10004d09
// vcipherlast %v1, %v1, %v9
.long 0x10214d09
// vcipherlast %v2, %v2, %v9
.long 0x10424d09
// vcipherlast %v3, %v3, %v9
.long 0x10634d09
// vcipherlast %v4, %v4, %v9
.long 0x10844d09
// vcipherlast %v5, %v5, %v9
.long 0x10a54d09
// vcipherlast %v6, %v6, %v9
.long 0x10c64d09
// vcipherlast %v7, %v7, %v9
.long 0x10e74d09
// cmpldi %cr0, %r19, 0
.long 0x28330000
beq %cr0, 211f
// rldicl %r12, %r19, 61, 3
.long 0x7a6ce8c2
// cmpldi %cr0, %r12, 0
.long 0x282c0000
bne %cr0, 213f
// addi %r12, %r19, -1
.long 0x3993ffff
// rldicl %r12, %r12, 1, 63
.long 0x798c0fe0
// cmpldi %cr0, %r12, 0
.long 0x282c0000
beq %cr0, 215f
// lxvd2x 40, %r6, %r0
.long 0x7d060699
b 216f
215:
// lxvd2x 40, %r17, %r0
.long 0x7d110699
216:
// addi %r12, %r19, -2
.long 0x3993fffe
// rldicl %r12, %r12, 1, 63
.long 0x798c0fe0
// cmpldi %cr0, %r12, 0
.long 0x282c0000
beq %cr0, 217f
// lxvd2x 41, %r6, %r20
.long 0x7d26a699
b 218f
217:
// lxvd2x 41, %r17, %r20
.long 0x7d31a699
218:
// addi %r12, %r19, -3
.long 0x3993fffd
// rldicl %r12, %r12, 1, 63
.long 0x798c0fe0
// cmpldi %cr0, %r12, 0
.long 0x282c0000
beq %cr0, 219f
// lxvd2x 43, %r6, %r21
.long 0x7d66ae99
b 220f
219:
// lxvd2x 43, %r17, %r21
.long 0x7d71ae99
220:
// addi %r12, %r19, -4
.long 0x3993fffc
// rldicl %r12, %r12, 1, 63
.long 0x798c0fe0
// cmpldi %cr0, %r12, 0
.long 0x282c0000
beq %cr0, 221f
// lxvd2x 44, %r6, %r22
.long 0x7d86b699
b 222f
221:
// lxvd2x 44, %r17, %r22
.long 0x7d91b699
222:
// addi %r12, %r19, -5
.long 0x3993fffb
// rldicl %r12, %r12, 1, 63
.long 0x798c0fe0
// cmpldi %cr0, %r12, 0
.long 0x282c0000
beq %cr0, 223f
// lxvd2x 46, %r6, %r23
.long 0x7dc6be99
b 224f
223:
// lxvd2x 46, %r17, %r23
.long 0x7dd1be99
224:
// addi %r12, %r19, -6
.long 0x3993fffa
// rldicl %r12, %r12, 1, 63
.long 0x798c0fe0
// cmpldi %cr0, %r12, 0
.long 0x282c0000
beq %cr0, 225f
// lxvd2x 47, %r6, %r24
.long 0x7de6c699
b 226f
225:
// lxvd2x 47, %r17, %r24
.long 0x7df1c699
226:
// addi %r12, %r19, -7
.long 0x3993fff9
// rldicl %r12, %r12, 1, 63
.long 0x798c0fe0
// cmpldi %cr0, %r12, 0
.long 0x282c0000
beq %cr0, 227f
// lxvd2x 48, %r6, %r18
.long 0x7e069699
b 228f
227:
// lxvd2x 48, %r17, %r18
.long 0x7e119699
228:
// addi %r12, %r19, -8
.long 0x3993fff8
// rldicl %r12, %r12, 1, 63
.long 0x798c0fe0
// cmpldi %cr0, %r12, 0
.long 0x282c0000
beq %cr0, 229f
// lxvd2x 49, %r6, %r11
.long 0x7e265e99
b 230f
229:
// lxvd2x 49, %r17, %r11
.long 0x7e315e99
230:
// rldicr %r12, %r19, 4, 59
.long 0x7a6c26e4
// add %r17, %r17, %r12
.long 0x7e316214
// li %r19, 0
.long 0x3a600000
b 214f
213:
// lxvd2x 40, %r17, %r0
.long 0x7d110699
// lxvd2x 41, %r17, %r20
.long 0x7d31a699
// lxvd2x 43, %r17, %r21
.long 0x7d71ae99
// lxvd2x 44, %r17, %r22
.long 0x7d91b699
// lxvd2x 46, %r17, %r23
.long 0x7dd1be99
// lxvd2x 47, %r17, %r24
.long 0x7df1c699
// lxvd2x 48, %r17, %r18
.long 0x7e119699
// lxvd2x 49, %r17, %r11
.long 0x7e315e99
// addi %r17, %r17, 128
.long 0x3a310080
// addi %r19, %r19, -8
.long 0x3a73fff8
214:
b 212f
211:
// lxvd2x 40, %r6, %r0
.long 0x7d060699
// lxvd2x 41, %r6, %r20
.long 0x7d26a699
// lxvd2x 43, %r6, %r21
.long 0x7d66ae99
// lxvd2x 44, %r6, %r22
.long 0x7d86b699
// lxvd2x 46, %r6, %r23
.long 0x7dc6be99
// lxvd2x 47, %r6, %r24
.long 0x7de6c699
// lxvd2x 48, %r6, %r18
.long 0x7e069699
// lxvd2x 49, %r6, %r11
.long 0x7e265e99
212:
// vperm %v8, %v8, %v8, %v19
.long 0x110844eb
// vxor %v0, %v0, %v8
.long 0x100044c4
// vperm %v9, %v9, %v9, %v19
.long 0x11294ceb
// vxor %v1, %v1, %v9
.long 0x10214cc4
// vperm %v11, %v11, %v11, %v19
.long 0x116b5ceb
// vxor %v2, %v2, %v11
.long 0x10425cc4
// vperm %v12, %v12, %v12, %v19
.long 0x118c64eb
// vxor %v3, %v3, %v12
.long 0x106364c4
// vperm %v14, %v14, %v14, %v19
.long 0x11ce74eb
// vxor %v4, %v4, %v14
.long 0x108474c4
// vperm %v15, %v15, %v15, %v19
.long 0x11ef7ceb
// vxor %v5, %v5, %v15
.long 0x10a57cc4
// vperm %v16, %v16, %v16, %v19
.long 0x121084eb
// vxor %v6, %v6, %v16
.long 0x10c684c4
// vperm %v17, %v17, %v17, %v19
.long 0x12318ceb
// vxor %v7, %v7, %v17
.long 0x10e78cc4
// vperm %v8, %v0, %v0, %v19
.long 0x110004eb
// stxvd2x 40, %r6, %r0
.long 0x7d060799
// vperm %v9, %v1, %v1, %v19
.long 0x11210ceb
// stxvd2x 41, %r6, %r20
.long 0x7d26a799
// vperm %v11, %v2, %v2, %v19
.long 0x116214eb
// stxvd2x 43, %r6, %r21
.long 0x7d66af99
// vperm %v12, %v3, %v3, %v19
.long 0x11831ceb
// stxvd2x 44, %r6, %r22
.long 0x7d86b799
// vperm %v14, %v4, %v4, %v19
.long 0x11c424eb
// stxvd2x 46, %r6, %r23
.long 0x7dc6bf99
// vperm %v15, %v5, %v5, %v19
.long 0x11e52ceb
// stxvd2x 47, %r6, %r24
.long 0x7de6c799
// vperm %v16, %v6, %v6, %v19
.long 0x120634eb
// stxvd2x 48, %r6, %r18
.long 0x7e069799
// vperm %v17, %v7, %v7, %v19
.long 0x12273ceb
// stxvd2x 49, %r6, %r11
.long 0x7e265f99
// addi %r6, %r6, 128
.long 0x38c60080
// addi %r7, %r7, -8
.long 0x38e7fff8
// lxvd2x 51, %r16, %r21
.long 0x7e70ae99
// lxvd2x 45, %r16, %r22
.long 0x7db0b699
// li %r21, 128
.long 0x3aa00080
// li %r22, 144
.long 0x3ac00090
// vxor %v0, %v0, %v10
.long 0x100054c4
// lxvd2x 40, %r16, %r21
.long 0x7d10ae99
// lxvd2x 41, %r16, %r22
.long 0x7d30b699
// addi %r21, %r21, 32
.long 0x3ab50020
// addi %r22, %r22, 32
.long 0x3ad60020
// vperm %v18, %v0, %v1, %v19
.long 0x12400ceb
// vperm %v17, %v0, %v1, %v13
.long 0x12200b6b
// vpmsumd %v16, %v17, %v9
.long 0x12114cc8
// vpmsumd %v14, %v18, %v8
.long 0x11d244c8
// vpmsumd %v15, %v17, %v8
.long 0x11f144c8
// vpmsumd %v17, %v18, %v9
.long 0x12324cc8
// vxor %v15, %v15, %v17
.long 0x11ef8cc4
// vor %v10, %v14, %v14
.long 0x114e7484
// vor %v11, %v15, %v15
.long 0x116f7c84
// vor %v12, %v16, %v16
.long 0x11908484
// lxvd2x 40, %r16, %r21
.long 0x7d10ae99
// lxvd2x 41, %r16, %r22
.long 0x7d30b699
// addi %r21, %r21, 32
.long 0x3ab50020
// addi %r22, %r22, 32
.long 0x3ad60020
// vperm %v18, %v2, %v3, %v19
.long 0x12421ceb
// vperm %v17, %v2, %v3, %v13
.long 0x12221b6b
// vpmsumd %v16, %v17, %v9
.long 0x12114cc8
// vpmsumd %v14, %v18, %v8
.long 0x11d244c8
// vpmsumd %v15, %v17, %v8
.long 0x11f144c8
// vpmsumd %v17, %v18, %v9
.long 0x12324cc8
// vxor %v15, %v15, %v17
.long 0x11ef8cc4
// vxor %v10, %v10, %v14
.long 0x114a74c4
// vxor %v11, %v11, %v15
.long 0x116b7cc4
// vxor %v12, %v12, %v16
.long 0x118c84c4
// lxvd2x 40, %r16, %r21
.long 0x7d10ae99
// lxvd2x 41, %r16, %r22
.long 0x7d30b699
// addi %r21, %r21, 32
.long 0x3ab50020
// addi %r22, %r22, 32
.long 0x3ad60020
// vperm %v18, %v4, %v5, %v19
.long 0x12442ceb
// vperm %v17, %v4, %v5, %v13
.long 0x12242b6b
// vpmsumd %v16, %v17, %v9
.long 0x12114cc8
// vpmsumd %v14, %v18, %v8
.long 0x11d244c8
// vpmsumd %v15, %v17, %v8
.long 0x11f144c8
// vpmsumd %v17, %v18, %v9
.long 0x12324cc8
// vxor %v15, %v15, %v17
.long 0x11ef8cc4
// vxor %v10, %v10, %v14
.long 0x114a74c4
// vxor %v11, %v11, %v15
.long 0x116b7cc4
// vxor %v12, %v12, %v16
.long 0x118c84c4
// lxvd2x 40, %r16, %r21
.long 0x7d10ae99
// lxvd2x 41, %r16, %r22
.long 0x7d30b699
// addi %r21, %r21, 32
.long 0x3ab50020
// addi %r22, %r22, 32
.long 0x3ad60020
// vperm %v18, %v6, %v7, %v19
.long 0x12463ceb
// vperm %v17, %v6, %v7, %v13
.long 0x12263b6b
// vpmsumd %v16, %v17, %v9
.long 0x12114cc8
// vpmsumd %v14, %v18, %v8
.long 0x11d244c8
// vpmsumd %v15, %v17, %v8
.long 0x11f144c8
// vpmsumd %v17, %v18, %v9
.long 0x12324cc8
// vxor %v15, %v15, %v17
.long 0x11ef8cc4
// vxor %v14, %v14, %v10
.long 0x11ce54c4
// vxor %v15, %v15, %v11
.long 0x11ef5cc4
// vxor %v16, %v16, %v12
.long 0x121064c4
// lxvd2x 51, %r16, %r24
.long 0x7e70c699
// lxvd2x 45, %r16, %r18
.long 0x7db09699
// vxor %v17, %v17, %v17
.long 0x12318cc4
// vsldoi %v18, %v14, %v17, 8
.long 0x124e8a2c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v17, 8
.long 0x124f8a2c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v10, %v16, %v18
.long 0x115094c4
// vsldoi %v10, %v10, %v10, 8
.long 0x114a522c
// cmpldi %cr0, %r7, 0
.long 0x28270000
bne %cr0, 27b
// li %r11, 12
.long 0x3960000c
// stwbrx %r8, %r5, %r11
.long 0x7d055d2c
// vperm %v10, %v10, %v10, %v19
.long 0x114a54eb
// stxvd2x 42, %r14, %r0
.long 0x7d4e0799
// addi %r12, %r16, -128
.long 0x3990ff80
// ld %r14, 0(%r12)
.long 0xe9cc0000
// ld %r15, 8(%r12)
.long 0xe9ec0008
// ld %r16, 16(%r12)
.long 0xea0c0010
// ld %r20, 40(%r12)
.long 0xea8c0028
// ld %r21, 48(%r12)
.long 0xeaac0030
// ld %r22, 56(%r12)
.long 0xeacc0038
// ld %r23, 64(%r12)
.long 0xeaec0040
// ld %r24, 72(%r12)
.long 0xeb0c0048
// ld %r18, 80(%r12)
.long 0xea4c0050
b 25f
24:
25:
// li %r0, 7
.long 0x38000007
// and %r11, %r25, %r0
.long 0x7f2b0038
// subf %r12, %r11, %r25
.long 0x7d8bc850
// rldicr %r12, %r12, 4, 59
.long 0x798c26e4
// add %r30, %r30, %r12
.long 0x7fde6214
// or %r25, %r11, %r11
.long 0x7d795b78
b 23f
22:
23:
// cmpldi %cr0, %r19, 0
.long 0x28330000
beq %cr0, 231f
// or %r11, %r30, %r30
.long 0x7fcbf378
// li %r0, 0
.long 0x38000000
233:
// lxvd2x 49, %r17, %r0
.long 0x7e310699
// stxvd2x 49, %r11, %r0
.long 0x7e2b0799
// addi %r17, %r17, 16
.long 0x3a310010
// addi %r11, %r11, 16
.long 0x396b0010
// addi %r19, %r19, -1
.long 0x3a73ffff
// cmpldi %cr0, %r19, 0
.long 0x28330000
bne %cr0, 233b
b 232f
231:
232:
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 234f
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// or %r5, %r27, %r27
.long 0x7f65db78
// or %r6, %r30, %r30
.long 0x7fc6f378
// or %r7, %r25, %r25
.long 0x7f27cb78
// addi %r8, %r31, 64
.long 0x391f0040
bl vg_aes_ctr32
// addi %r3, %r29, 240
.long 0x387d00f0
// or %r4, %r26, %r26
.long 0x7f44d378
// or %r5, %r30, %r30
.long 0x7fc5f378
// or %r6, %r25, %r25
.long 0x7f26cb78
// addi %r7, %r31, 64
.long 0x38ff0040
bl vg_ghash
b 235f
234:
235:
// ld %r0, 56(%r31)
.long 0xe81f0038
// mtlr %r0
.long 0x7c0803a6
// or %r12, %r31, %r31
.long 0x7fecfb78
// ld %r25, 0(%r12)
.long 0xeb2c0000
// ld %r26, 8(%r12)
.long 0xeb4c0008
// ld %r27, 16(%r12)
.long 0xeb6c0010
// ld %r28, 24(%r12)
.long 0xeb8c0018
// ld %r29, 32(%r12)
.long 0xebac0020
// ld %r30, 40(%r12)
.long 0xebcc0028
// ld %r31, 48(%r12)
.long 0xebec0030
b 21f
20:
21:
// blr
.long 0x4e800020
.globl vg_aes_gcm_encrypt_blocks
.type vg_aes_gcm_encrypt_blocks,@function
vg_aes_gcm_encrypt_blocks:
// cmpldi %cr0, %r8, 0
.long 0x28280000
beq %cr0, 20f
// std %r25, 0(%r9)
.long 0xfb290000
// std %r26, 8(%r9)
.long 0xfb490008
// std %r27, 16(%r9)
.long 0xfb690010
// std %r28, 24(%r9)
.long 0xfb890018
// std %r29, 32(%r9)
.long 0xfba90020
// std %r30, 40(%r9)
.long 0xfbc90028
// std %r31, 48(%r9)
.long 0xfbe90030
// mflr %r0
.long 0x7c0802a6
// std %r0, 56(%r9)
.long 0xf8090038
// or %r29, %r3, %r3
.long 0x7c7d1b78
// or %r28, %r4, %r4
.long 0x7c9c2378
// or %r27, %r5, %r5
.long 0x7cbb2b78
// or %r26, %r6, %r6
.long 0x7cda3378
// or %r30, %r7, %r7
.long 0x7cfe3b78
// or %r25, %r8, %r8
.long 0x7d194378
// or %r31, %r9, %r9
.long 0x7d3f4b78
// rldicl %r12, %r25, 59, 5
.long 0x7b2cd942
// cmpldi %cr0, %r12, 0
.long 0x282c0000
beq %cr0, 22f
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// or %r5, %r27, %r27
.long 0x7f65db78
// or %r6, %r30, %r30
.long 0x7fc6f378
// li %r0, 7
.long 0x38000007
// and %r11, %r25, %r0
.long 0x7f2b0038
// subf %r7, %r11, %r25
.long 0x7cebc850
// addi %r8, %r29, 240
.long 0x391d00f0
// or %r9, %r26, %r26
.long 0x7f49d378
// addi %r10, %r31, 64
.long 0x395f0040
// cmpldi %cr0, %r7, 0
.long 0x28270000
beq %cr0, 24f
// std %r14, 0(%r10)
.long 0xf9ca0000
// std %r15, 8(%r10)
.long 0xf9ea0008
// std %r16, 16(%r10)
.long 0xfa0a0010
// std %r20, 40(%r10)
.long 0xfa8a0028
// std %r21, 48(%r10)
.long 0xfaaa0030
// std %r22, 56(%r10)
.long 0xfaca0038
// std %r23, 64(%r10)
.long 0xfaea0040
// std %r24, 72(%r10)
.long 0xfb0a0048
// std %r18, 80(%r10)
.long 0xfa4a0050
// or %r16, %r10, %r10
.long 0x7d505378
// addi %r16, %r16, 128
.long 0x3a100080
// or %r14, %r9, %r9
.long 0x7d2e4b78
// li %r15, 112
.long 0x39e00070
// li %r0, 0
.long 0x38000000
// vxor %v0, %v0, %v0
.long 0x100004c4
// lis %r11, 1798
.long 0x3d600706
// ori %r11, %r11, 1284
.long 0x616b0504
// rldicr %r11, %r11, 32, 31
.long 0x796b07c6
// oris %r11, %r11, 770
.long 0x656b0302
// ori %r11, %r11, 256
.long 0x616b0100
// lis %r12, 3854
.long 0x3d800f0e
// ori %r12, %r12, 3340
.long 0x618c0d0c
// rldicr %r12, %r12, 32, 31
.long 0x798c07c6
// oris %r12, %r12, 2826
.long 0x658c0b0a
// ori %r12, %r12, 2312
.long 0x618c0908
// mtvsrd 51, %r11
.long 0x7e6b0167
// mtvsrd 33, %r12
.long 0x7c2c0167
// vsldoi %v19, %v0, %v19, 8
.long 0x12609a2c
// vsldoi %v19, %v19, %v1, 8
.long 0x12730a2c
// li %r20, 16
.long 0x3a800010
// addi %r24, %r16, 256
.long 0x3b100100
// li %r18, 96
.long 0x3a400060
// lis %r11, 0
.long 0x3d600000
// ori %r11, %r11, 0
.long 0x616b0000
// rldicr %r11, %r11, 32, 31
.long 0x796b07c6
// oris %r11, %r11, 0
.long 0x656b0000
// ori %r11, %r11, 0
.long 0x616b0000
// lis %r12, 0
.long 0x3d800000
// ori %r12, %r12, 0
.long 0x618c0000
// rldicr %r12, %r12, 32, 31
.long 0x798c07c6
// oris %r12, %r12, 0
.long 0x658c0000
// ori %r12, %r12, 1
.long 0x618c0001
// mtvsrd 49, %r11
.long 0x7e2b0167
// mtvsrd 33, %r12
.long 0x7c2c0167
// vsldoi %v17, %v0, %v17, 8
.long 0x12208a2c
// vsldoi %v17, %v17, %v1, 8
.long 0x12310a2c
// stxvd2x 49, %r16, %r20
.long 0x7e30a799
// lis %r11, -15872
.long 0x3d60c200
// ori %r11, %r11, 0
.long 0x616b0000
// rldicr %r11, %r11, 32, 31
.long 0x796b07c6
// oris %r11, %r11, 0
.long 0x656b0000
// ori %r11, %r11, 0
.long 0x616b0000
// lis %r12, -15872
.long 0x3d80c200
// ori %r12, %r12, 0
.long 0x618c0000
// rldicr %r12, %r12, 32, 31
.long 0x798c07c6
// oris %r12, %r12, 0
.long 0x658c0000
// ori %r12, %r12, 0
.long 0x618c0000
// mtvsrd 45, %r11
.long 0x7dab0167
// mtvsrd 33, %r12
.long 0x7c2c0167
// vsldoi %v13, %v0, %v13, 8
.long 0x11a06a2c
// vsldoi %v13, %v13, %v1, 8
.long 0x11ad0a2c
// lis %r11, 17920
.long 0x3d604600
// ori %r11, %r11, 0
.long 0x616b0000
// rldicr %r11, %r11, 32, 31
.long 0x796b07c6
// oris %r11, %r11, 0
.long 0x656b0000
// ori %r11, %r11, 0
.long 0x616b0000
// lis %r12, 0
.long 0x3d800000
// ori %r12, %r12, 0
.long 0x618c0000
// rldicr %r12, %r12, 32, 31
.long 0x798c07c6
// oris %r12, %r12, 0
.long 0x658c0000
// ori %r12, %r12, 3
.long 0x618c0003
// mtvsrd 43, %r11
.long 0x7d6b0167
// mtvsrd 33, %r12
.long 0x7c2c0167
// vsldoi %v11, %v0, %v11, 8
.long 0x11605a2c
// vsldoi %v11, %v11, %v1, 8
.long 0x116b0a2c
// lxvd2x 41, %r8, %r0
.long 0x7d280699
// vperm %v9, %v9, %v9, %v19
.long 0x11294ceb
// vsldoi %v9, %v9, %v9, 8
.long 0x11294a2c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v11, %v16, %v18
.long 0x117094c4
// vsldoi %v11, %v11, %v11, 8
.long 0x116b5a2c
// lxvd2x 42, %r14, %r0
.long 0x7d4e0699
// vperm %v10, %v10, %v10, %v19
.long 0x114a54eb
// li %r11, 12
.long 0x3960000c
// lwbrx %r8, %r5, %r11
.long 0x7d055c2c
// or %r9, %r3, %r3
.long 0x7c691b78
// vor %v12, %v11, %v11
.long 0x118b5c84
// vor %v8, %v12, %v12
.long 0x110c6484
// vsldoi %v9, %v12, %v12, 8
.long 0x112c622c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v12, %v16, %v18
.long 0x119094c4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vsldoi %v9, %v8, %v8, 8
.long 0x1128422c
// vsldoi %v18, %v9, %v12, 8
.long 0x1249622c
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vsldoi %v8, %v12, %v9, 8
.long 0x110c4a2c
// li %r11, 224
.long 0x396000e0
// stxvd2x 40, %r16, %r11
.long 0x7d105f99
// li %r11, 240
.long 0x396000f0
// stxvd2x 50, %r16, %r11
.long 0x7e505f99
// vsldoi %v9, %v12, %v12, 8
.long 0x112c622c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v12, %v16, %v18
.long 0x119094c4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vor %v8, %v12, %v12
.long 0x110c6484
// vsldoi %v9, %v12, %v12, 8
.long 0x112c622c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v12, %v16, %v18
.long 0x119094c4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vsldoi %v9, %v8, %v8, 8
.long 0x1128422c
// vsldoi %v18, %v9, %v12, 8
.long 0x1249622c
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vsldoi %v8, %v12, %v9, 8
.long 0x110c4a2c
// li %r11, 192
.long 0x396000c0
// stxvd2x 40, %r16, %r11
.long 0x7d105f99
// li %r11, 208
.long 0x396000d0
// stxvd2x 50, %r16, %r11
.long 0x7e505f99
// vsldoi %v9, %v12, %v12, 8
.long 0x112c622c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v12, %v16, %v18
.long 0x119094c4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vor %v8, %v12, %v12
.long 0x110c6484
// vsldoi %v9, %v12, %v12, 8
.long 0x112c622c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v12, %v16, %v18
.long 0x119094c4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vsldoi %v9, %v8, %v8, 8
.long 0x1128422c
// vsldoi %v18, %v9, %v12, 8
.long 0x1249622c
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vsldoi %v8, %v12, %v9, 8
.long 0x110c4a2c
// li %r11, 160
.long 0x396000a0
// stxvd2x 40, %r16, %r11
.long 0x7d105f99
// li %r11, 176
.long 0x396000b0
// stxvd2x 50, %r16, %r11
.long 0x7e505f99
// vsldoi %v9, %v12, %v12, 8
.long 0x112c622c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v12, %v16, %v18
.long 0x119094c4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vor %v8, %v12, %v12
.long 0x110c6484
// vsldoi %v9, %v12, %v12, 8
.long 0x112c622c
// vsldoi %v17, %v9, %v0, 8
.long 0x1229022c
// vpmsumd %v16, %v17, %v11
.long 0x12115cc8
// vsldoi %v17, %v0, %v9, 8
.long 0x12204a2c
// vpmsumd %v14, %v17, %v11
.long 0x11d15cc8
// vpmsumd %v15, %v9, %v11
.long 0x11e95cc8
// vsldoi %v18, %v14, %v0, 8
.long 0x124e022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v0, 8
.long 0x124f022c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v12, %v16, %v18
.long 0x119094c4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vsldoi %v9, %v8, %v8, 8
.long 0x1128422c
// vsldoi %v18, %v9, %v12, 8
.long 0x1249622c
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vsldoi %v8, %v12, %v9, 8
.long 0x110c4a2c
// li %r11, 128
.long 0x39600080
// stxvd2x 40, %r16, %r11
.long 0x7d105f99
// li %r11, 144
.long 0x39600090
// stxvd2x 50, %r16, %r11
.long 0x7e505f99
// lis %r11, 2057
.long 0x3d600809
// ori %r11, %r11, 2571
.long 0x616b0a0b
// rldicr %r11, %r11, 32, 31
.long 0x796b07c6
// oris %r11, %r11, 3085
.long 0x656b0c0d
// ori %r11, %r11, 3599
.long 0x616b0e0f
// lis %r12, 6169
.long 0x3d801819
// ori %r12, %r12, 6683
.long 0x618c1a1b
// rldicr %r12, %r12, 32, 31
.long 0x798c07c6
// oris %r12, %r12, 7197
.long 0x658c1c1d
// ori %r12, %r12, 7711
.long 0x618c1e1f
// mtvsrd 49, %r11
.long 0x7e2b0167
// mtvsrd 33, %r12
.long 0x7c2c0167
// vsldoi %v17, %v0, %v17, 8
.long 0x12208a2c
// vsldoi %v17, %v17, %v1, 8
.long 0x12310a2c
// li %r11, 32
.long 0x39600020
// stxvd2x 49, %r16, %r11
.long 0x7e305f99
// lis %r11, 1
.long 0x3d600001
// ori %r11, %r11, 515
.long 0x616b0203
// rldicr %r11, %r11, 32, 31
.long 0x796b07c6
// oris %r11, %r11, 1029
.long 0x656b0405
// ori %r11, %r11, 1543
.long 0x616b0607
// lis %r12, 4113
.long 0x3d801011
// ori %r12, %r12, 4627
.long 0x618c1213
// rldicr %r12, %r12, 32, 31
.long 0x798c07c6
// oris %r12, %r12, 5141
.long 0x658c1415
// ori %r12, %r12, 5655
.long 0x618c1617
// mtvsrd 49, %r11
.long 0x7e2b0167
// mtvsrd 33, %r12
.long 0x7c2c0167
// vsldoi %v17, %v0, %v17, 8
.long 0x12208a2c
// vsldoi %v17, %v17, %v1, 8
.long 0x12310a2c
// li %r11, 48
.long 0x39600030
// stxvd2x 49, %r16, %r11
.long 0x7e305f99
// li %r11, 80
.long 0x39600050
// stxvd2x 51, %r16, %r11
.long 0x7e705f99
// li %r11, 96
.long 0x39600060
// stxvd2x 45, %r16, %r11
.long 0x7db05f99
// or %r11, %r24, %r24
.long 0x7f0bc378
// addi %r12, %r4, 1
.long 0x39840001
26:
// lxvd2x 40, %r9, %r0
.long 0x7d090699
// vperm %v8, %v8, %v8, %v19
.long 0x110844eb
// stxvd2x 40, %r11, %r0
.long 0x7d0b0799
// addi %r9, %r9, 16
.long 0x39290010
// addi %r11, %r11, 16
.long 0x396b0010
// addi %r12, %r12, -1
.long 0x398cffff
// cmpldi %cr0, %r12, 0
.long 0x282c0000
bne %cr0, 26b
// or %r3, %r24, %r24
.long 0x7f03c378
// li %r23, 64
.long 0x3ae00040
// li %r24, 80
.long 0x3b000050
// lxvd2x 32, %r5, %r0
.long 0x7c050699
// vperm %v0, %v0, %v0, %v19
.long 0x100004eb
// stxvd2x 32, %r16, %r15
.long 0x7c107f99
27:
// lxvd2x 32, %r16, %r15
.long 0x7c107e99
// lxvd2x 49, %r16, %r20
.long 0x7e30a699
// vadduwm %v18, %v17, %v17
.long 0x12518880
// vadduwm %v1, %v0, %v17
.long 0x10208880
// vadduwm %v2, %v0, %v18
.long 0x10409080
// vadduwm %v3, %v1, %v18
.long 0x10619080
// vadduwm %v4, %v2, %v18
.long 0x10829080
// vadduwm %v5, %v3, %v18
.long 0x10a39080
// vadduwm %v6, %v4, %v18
.long 0x10c49080
// vadduwm %v7, %v5, %v18
.long 0x10e59080
// vadduwm %v18, %v6, %v18
.long 0x12469080
// stxvd2x 50, %r16, %r15
.long 0x7e507f99
// addi %r8, %r8, 8
.long 0x39080008
// lxvd2x 40, %r3, %r0
.long 0x7d030699
// vxor %v0, %v0, %v8
.long 0x100044c4
// vxor %v1, %v1, %v8
.long 0x102144c4
// vxor %v2, %v2, %v8
.long 0x104244c4
// vxor %v3, %v3, %v8
.long 0x106344c4
// vxor %v4, %v4, %v8
.long 0x108444c4
// vxor %v5, %v5, %v8
.long 0x10a544c4
// vxor %v6, %v6, %v8
.long 0x10c644c4
// vxor %v7, %v7, %v8
.long 0x10e744c4
// lxvd2x 40, %r3, %r20
.long 0x7d03a699
// li %r21, 32
.long 0x3aa00020
// lxvd2x 41, %r3, %r21
.long 0x7d23ae99
// li %r22, 48
.long 0x3ac00030
// lxvd2x 43, %r3, %r22
.long 0x7d63b699
// lxvd2x 44, %r3, %r23
.long 0x7d83be99
// lxvd2x 46, %r3, %r24
.long 0x7dc3c699
// lxvd2x 47, %r3, %r18
.long 0x7de39699
// li %r11, 112
.long 0x39600070
// lxvd2x 48, %r3, %r11
.long 0x7e035e99
// li %r12, 128
.long 0x39800080
// lxvd2x 49, %r3, %r12
.long 0x7e236699
// addi %r9, %r3, 144
.long 0x39230090
// lxvd2x 50, %r9, %r0
.long 0x7e490699
// vcipher %v0, %v0, %v8
.long 0x10004508
// vcipher %v1, %v1, %v8
.long 0x10214508
// vcipher %v2, %v2, %v8
.long 0x10424508
// vcipher %v3, %v3, %v8
.long 0x10634508
// vcipher %v4, %v4, %v8
.long 0x10844508
// vcipher %v5, %v5, %v8
.long 0x10a54508
// vcipher %v6, %v6, %v8
.long 0x10c64508
// vcipher %v7, %v7, %v8
.long 0x10e74508
// vcipher %v0, %v0, %v9
.long 0x10004d08
// vcipher %v1, %v1, %v9
.long 0x10214d08
// vcipher %v2, %v2, %v9
.long 0x10424d08
// vcipher %v3, %v3, %v9
.long 0x10634d08
// vcipher %v4, %v4, %v9
.long 0x10844d08
// vcipher %v5, %v5, %v9
.long 0x10a54d08
// vcipher %v6, %v6, %v9
.long 0x10c64d08
// vcipher %v7, %v7, %v9
.long 0x10e74d08
// rldicr %r12, %r4, 4, 59
.long 0x788c26e4
// lxvd2x 41, %r3, %r12
.long 0x7d236699
// vcipher %v0, %v0, %v11
.long 0x10005d08
// vcipher %v1, %v1, %v11
.long 0x10215d08
// vcipher %v2, %v2, %v11
.long 0x10425d08
// vcipher %v3, %v3, %v11
.long 0x10635d08
// vcipher %v4, %v4, %v11
.long 0x10845d08
// vcipher %v5, %v5, %v11
.long 0x10a55d08
// vcipher %v6, %v6, %v11
.long 0x10c65d08
// vcipher %v7, %v7, %v11
.long 0x10e75d08
// vcipher %v0, %v0, %v12
.long 0x10006508
// vcipher %v1, %v1, %v12
.long 0x10216508
// vcipher %v2, %v2, %v12
.long 0x10426508
// vcipher %v3, %v3, %v12
.long 0x10636508
// vcipher %v4, %v4, %v12
.long 0x10846508
// vcipher %v5, %v5, %v12
.long 0x10a56508
// vcipher %v6, %v6, %v12
.long 0x10c66508
// vcipher %v7, %v7, %v12
.long 0x10e76508
// vcipher %v0, %v0, %v14
.long 0x10007508
// vcipher %v1, %v1, %v14
.long 0x10217508
// vcipher %v2, %v2, %v14
.long 0x10427508
// vcipher %v3, %v3, %v14
.long 0x10637508
// vcipher %v4, %v4, %v14
.long 0x10847508
// vcipher %v5, %v5, %v14
.long 0x10a57508
// vcipher %v6, %v6, %v14
.long 0x10c67508
// vcipher %v7, %v7, %v14
.long 0x10e77508
// vcipher %v0, %v0, %v15
.long 0x10007d08
// vcipher %v1, %v1, %v15
.long 0x10217d08
// vcipher %v2, %v2, %v15
.long 0x10427d08
// vcipher %v3, %v3, %v15
.long 0x10637d08
// vcipher %v4, %v4, %v15
.long 0x10847d08
// vcipher %v5, %v5, %v15
.long 0x10a57d08
// vcipher %v6, %v6, %v15
.long 0x10c67d08
// vcipher %v7, %v7, %v15
.long 0x10e77d08
// vcipher %v0, %v0, %v16
.long 0x10008508
// vcipher %v1, %v1, %v16
.long 0x10218508
// vcipher %v2, %v2, %v16
.long 0x10428508
// vcipher %v3, %v3, %v16
.long 0x10638508
// vcipher %v4, %v4, %v16
.long 0x10848508
// vcipher %v5, %v5, %v16
.long 0x10a58508
// vcipher %v6, %v6, %v16
.long 0x10c68508
// vcipher %v7, %v7, %v16
.long 0x10e78508
// vcipher %v0, %v0, %v17
.long 0x10008d08
// vcipher %v1, %v1, %v17
.long 0x10218d08
// vcipher %v2, %v2, %v17
.long 0x10428d08
// vcipher %v3, %v3, %v17
.long 0x10638d08
// vcipher %v4, %v4, %v17
.long 0x10848d08
// vcipher %v5, %v5, %v17
.long 0x10a58d08
// vcipher %v6, %v6, %v17
.long 0x10c68d08
// vcipher %v7, %v7, %v17
.long 0x10e78d08
// vcipher %v0, %v0, %v18
.long 0x10009508
// vcipher %v1, %v1, %v18
.long 0x10219508
// vcipher %v2, %v2, %v18
.long 0x10429508
// vcipher %v3, %v3, %v18
.long 0x10639508
// vcipher %v4, %v4, %v18
.long 0x10849508
// vcipher %v5, %v5, %v18
.long 0x10a59508
// vcipher %v6, %v6, %v18
.long 0x10c69508
// vcipher %v7, %v7, %v18
.long 0x10e79508
// addi %r9, %r3, 160
.long 0x392300a0
// addi %r10, %r4, -10
.long 0x3944fff6
// cmpldi %cr0, %r10, 0
.long 0x282a0000
beq %cr0, 28f
210:
// lxvd2x 40, %r9, %r0
.long 0x7d090699
// vcipher %v0, %v0, %v8
.long 0x10004508
// vcipher %v1, %v1, %v8
.long 0x10214508
// vcipher %v2, %v2, %v8
.long 0x10424508
// vcipher %v3, %v3, %v8
.long 0x10634508
// vcipher %v4, %v4, %v8
.long 0x10844508
// vcipher %v5, %v5, %v8
.long 0x10a54508
// vcipher %v6, %v6, %v8
.long 0x10c64508
// vcipher %v7, %v7, %v8
.long 0x10e74508
// addi %r9, %r9, 16
.long 0x39290010
// addi %r10, %r10, -1
.long 0x394affff
// cmpldi %cr0, %r10, 0
.long 0x282a0000
bne %cr0, 210b
b 29f
28:
29:
// vcipherlast %v0, %v0, %v9
.long 0x10004d09
// vcipherlast %v1, %v1, %v9
.long 0x10214d09
// vcipherlast %v2, %v2, %v9
.long 0x10424d09
// vcipherlast %v3, %v3, %v9
.long 0x10634d09
// vcipherlast %v4, %v4, %v9
.long 0x10844d09
// vcipherlast %v5, %v5, %v9
.long 0x10a54d09
// vcipherlast %v6, %v6, %v9
.long 0x10c64d09
// vcipherlast %v7, %v7, %v9
.long 0x10e74d09
// lxvd2x 40, %r6, %r0
.long 0x7d060699
// lxvd2x 41, %r6, %r20
.long 0x7d26a699
// lxvd2x 43, %r6, %r21
.long 0x7d66ae99
// lxvd2x 44, %r6, %r22
.long 0x7d86b699
// lxvd2x 46, %r6, %r23
.long 0x7dc6be99
// lxvd2x 47, %r6, %r24
.long 0x7de6c699
// lxvd2x 48, %r6, %r18
.long 0x7e069699
// lxvd2x 49, %r6, %r11
.long 0x7e265e99
// vperm %v8, %v8, %v8, %v19
.long 0x110844eb
// vxor %v0, %v0, %v8
.long 0x100044c4
// vperm %v9, %v9, %v9, %v19
.long 0x11294ceb
// vxor %v1, %v1, %v9
.long 0x10214cc4
// vperm %v11, %v11, %v11, %v19
.long 0x116b5ceb
// vxor %v2, %v2, %v11
.long 0x10425cc4
// vperm %v12, %v12, %v12, %v19
.long 0x118c64eb
// vxor %v3, %v3, %v12
.long 0x106364c4
// vperm %v14, %v14, %v14, %v19
.long 0x11ce74eb
// vxor %v4, %v4, %v14
.long 0x108474c4
// vperm %v15, %v15, %v15, %v19
.long 0x11ef7ceb
// vxor %v5, %v5, %v15
.long 0x10a57cc4
// vperm %v16, %v16, %v16, %v19
.long 0x121084eb
// vxor %v6, %v6, %v16
.long 0x10c684c4
// vperm %v17, %v17, %v17, %v19
.long 0x12318ceb
// vxor %v7, %v7, %v17
.long 0x10e78cc4
// vperm %v8, %v0, %v0, %v19
.long 0x110004eb
// stxvd2x 40, %r6, %r0
.long 0x7d060799
// vperm %v9, %v1, %v1, %v19
.long 0x11210ceb
// stxvd2x 41, %r6, %r20
.long 0x7d26a799
// vperm %v11, %v2, %v2, %v19
.long 0x116214eb
// stxvd2x 43, %r6, %r21
.long 0x7d66af99
// vperm %v12, %v3, %v3, %v19
.long 0x11831ceb
// stxvd2x 44, %r6, %r22
.long 0x7d86b799
// vperm %v14, %v4, %v4, %v19
.long 0x11c424eb
// stxvd2x 46, %r6, %r23
.long 0x7dc6bf99
// vperm %v15, %v5, %v5, %v19
.long 0x11e52ceb
// stxvd2x 47, %r6, %r24
.long 0x7de6c799
// vperm %v16, %v6, %v6, %v19
.long 0x120634eb
// stxvd2x 48, %r6, %r18
.long 0x7e069799
// vperm %v17, %v7, %v7, %v19
.long 0x12273ceb
// stxvd2x 49, %r6, %r11
.long 0x7e265f99
// addi %r6, %r6, 128
.long 0x38c60080
// addi %r7, %r7, -8
.long 0x38e7fff8
// lxvd2x 51, %r16, %r21
.long 0x7e70ae99
// lxvd2x 45, %r16, %r22
.long 0x7db0b699
// li %r21, 128
.long 0x3aa00080
// li %r22, 144
.long 0x3ac00090
// vxor %v0, %v0, %v10
.long 0x100054c4
// lxvd2x 40, %r16, %r21
.long 0x7d10ae99
// lxvd2x 41, %r16, %r22
.long 0x7d30b699
// addi %r21, %r21, 32
.long 0x3ab50020
// addi %r22, %r22, 32
.long 0x3ad60020
// vperm %v18, %v0, %v1, %v19
.long 0x12400ceb
// vperm %v17, %v0, %v1, %v13
.long 0x12200b6b
// vpmsumd %v16, %v17, %v9
.long 0x12114cc8
// vpmsumd %v14, %v18, %v8
.long 0x11d244c8
// vpmsumd %v15, %v17, %v8
.long 0x11f144c8
// vpmsumd %v17, %v18, %v9
.long 0x12324cc8
// vxor %v15, %v15, %v17
.long 0x11ef8cc4
// vor %v10, %v14, %v14
.long 0x114e7484
// vor %v11, %v15, %v15
.long 0x116f7c84
// vor %v12, %v16, %v16
.long 0x11908484
// lxvd2x 40, %r16, %r21
.long 0x7d10ae99
// lxvd2x 41, %r16, %r22
.long 0x7d30b699
// addi %r21, %r21, 32
.long 0x3ab50020
// addi %r22, %r22, 32
.long 0x3ad60020
// vperm %v18, %v2, %v3, %v19
.long 0x12421ceb
// vperm %v17, %v2, %v3, %v13
.long 0x12221b6b
// vpmsumd %v16, %v17, %v9
.long 0x12114cc8
// vpmsumd %v14, %v18, %v8
.long 0x11d244c8
// vpmsumd %v15, %v17, %v8
.long 0x11f144c8
// vpmsumd %v17, %v18, %v9
.long 0x12324cc8
// vxor %v15, %v15, %v17
.long 0x11ef8cc4
// vxor %v10, %v10, %v14
.long 0x114a74c4
// vxor %v11, %v11, %v15
.long 0x116b7cc4
// vxor %v12, %v12, %v16
.long 0x118c84c4
// lxvd2x 40, %r16, %r21
.long 0x7d10ae99
// lxvd2x 41, %r16, %r22
.long 0x7d30b699
// addi %r21, %r21, 32
.long 0x3ab50020
// addi %r22, %r22, 32
.long 0x3ad60020
// vperm %v18, %v4, %v5, %v19
.long 0x12442ceb
// vperm %v17, %v4, %v5, %v13
.long 0x12242b6b
// vpmsumd %v16, %v17, %v9
.long 0x12114cc8
// vpmsumd %v14, %v18, %v8
.long 0x11d244c8
// vpmsumd %v15, %v17, %v8
.long 0x11f144c8
// vpmsumd %v17, %v18, %v9
.long 0x12324cc8
// vxor %v15, %v15, %v17
.long 0x11ef8cc4
// vxor %v10, %v10, %v14
.long 0x114a74c4
// vxor %v11, %v11, %v15
.long 0x116b7cc4
// vxor %v12, %v12, %v16
.long 0x118c84c4
// lxvd2x 40, %r16, %r21
.long 0x7d10ae99
// lxvd2x 41, %r16, %r22
.long 0x7d30b699
// addi %r21, %r21, 32
.long 0x3ab50020
// addi %r22, %r22, 32
.long 0x3ad60020
// vperm %v18, %v6, %v7, %v19
.long 0x12463ceb
// vperm %v17, %v6, %v7, %v13
.long 0x12263b6b
// vpmsumd %v16, %v17, %v9
.long 0x12114cc8
// vpmsumd %v14, %v18, %v8
.long 0x11d244c8
// vpmsumd %v15, %v17, %v8
.long 0x11f144c8
// vpmsumd %v17, %v18, %v9
.long 0x12324cc8
// vxor %v15, %v15, %v17
.long 0x11ef8cc4
// vxor %v14, %v14, %v10
.long 0x11ce54c4
// vxor %v15, %v15, %v11
.long 0x11ef5cc4
// vxor %v16, %v16, %v12
.long 0x121064c4
// lxvd2x 51, %r16, %r24
.long 0x7e70c699
// lxvd2x 45, %r16, %r18
.long 0x7db09699
// vxor %v17, %v17, %v17
.long 0x12318cc4
// vsldoi %v18, %v14, %v17, 8
.long 0x124e8a2c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vxor %v15, %v15, %v14
.long 0x11ef74c4
// vxor %v15, %v15, %v18
.long 0x11ef94c4
// vsldoi %v18, %v15, %v17, 8
.long 0x124f8a2c
// vpmsumd %v18, %v18, %v13
.long 0x12526cc8
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// vxor %v16, %v16, %v15
.long 0x12107cc4
// vsldoi %v18, %v18, %v18, 8
.long 0x1252922c
// vxor %v10, %v16, %v18
.long 0x115094c4
// vsldoi %v10, %v10, %v10, 8
.long 0x114a522c
// cmpldi %cr0, %r7, 0
.long 0x28270000
bne %cr0, 27b
// li %r11, 12
.long 0x3960000c
// stwbrx %r8, %r5, %r11
.long 0x7d055d2c
// vperm %v10, %v10, %v10, %v19
.long 0x114a54eb
// stxvd2x 42, %r14, %r0
.long 0x7d4e0799
// addi %r12, %r16, -128
.long 0x3990ff80
// ld %r14, 0(%r12)
.long 0xe9cc0000
// ld %r15, 8(%r12)
.long 0xe9ec0008
// ld %r16, 16(%r12)
.long 0xea0c0010
// ld %r20, 40(%r12)
.long 0xea8c0028
// ld %r21, 48(%r12)
.long 0xeaac0030
// ld %r22, 56(%r12)
.long 0xeacc0038
// ld %r23, 64(%r12)
.long 0xeaec0040
// ld %r24, 72(%r12)
.long 0xeb0c0048
// ld %r18, 80(%r12)
.long 0xea4c0050
b 25f
24:
25:
// li %r0, 7
.long 0x38000007
// and %r11, %r25, %r0
.long 0x7f2b0038
// subf %r12, %r11, %r25
.long 0x7d8bc850
// rldicr %r12, %r12, 4, 59
.long 0x798c26e4
// add %r30, %r30, %r12
.long 0x7fde6214
// or %r25, %r11, %r11
.long 0x7d795b78
b 23f
22:
23:
// cmpldi %cr0, %r25, 0
.long 0x28390000
beq %cr0, 211f
// or %r3, %r29, %r29
.long 0x7fa3eb78
// or %r4, %r28, %r28
.long 0x7f84e378
// or %r5, %r27, %r27
.long 0x7f65db78
// or %r6, %r30, %r30
.long 0x7fc6f378
// or %r7, %r25, %r25
.long 0x7f27cb78
// addi %r8, %r31, 64
.long 0x391f0040
bl vg_aes_ctr32
// addi %r3, %r29, 240
.long 0x387d00f0
// or %r4, %r26, %r26
.long 0x7f44d378
// or %r5, %r30, %r30
.long 0x7fc5f378
// or %r6, %r25, %r25
.long 0x7f26cb78
// addi %r7, %r31, 64
.long 0x38ff0040
bl vg_ghash
b 212f
211:
212:
// ld %r0, 56(%r31)
.long 0xe81f0038
// mtlr %r0
.long 0x7c0803a6
// or %r12, %r31, %r31
.long 0x7fecfb78
// ld %r25, 0(%r12)
.long 0xeb2c0000
// ld %r26, 8(%r12)
.long 0xeb4c0008
// ld %r27, 16(%r12)
.long 0xeb6c0010
// ld %r28, 24(%r12)
.long 0xeb8c0018
// ld %r29, 32(%r12)
.long 0xebac0020
// ld %r30, 40(%r12)
.long 0xebcc0028
// ld %r31, 48(%r12)
.long 0xebec0030
b 21f
20:
21:
// blr
.long 0x4e800020
.globl vg_aes_ctr32
.type vg_aes_ctr32,@function
vg_aes_ctr32:
// cmpldi %cr0, %r7, 0
.long 0x28270000
beq %cr0, 20f
// li %r0, 0
.long 0x38000000
// vxor %v0, %v0, %v0
.long 0x100004c4
// lis %r11, 1798
.long 0x3d600706
// ori %r11, %r11, 1284
.long 0x616b0504
// rldicr %r11, %r11, 32, 31
.long 0x796b07c6
// oris %r11, %r11, 770
.long 0x656b0302
// ori %r11, %r11, 256
.long 0x616b0100
// lis %r12, 3854
.long 0x3d800f0e
// ori %r12, %r12, 3340
.long 0x618c0d0c
// rldicr %r12, %r12, 32, 31
.long 0x798c07c6
// oris %r12, %r12, 2826
.long 0x658c0b0a
// ori %r12, %r12, 2312
.long 0x618c0908
// mtvsrd 51, %r11
.long 0x7e6b0167
// mtvsrd 33, %r12
.long 0x7c2c0167
// vsldoi %v19, %v0, %v19, 8
.long 0x12609a2c
// vsldoi %v19, %v19, %v1, 8
.long 0x12730a2c
// lis %r11, 1
.long 0x3d600001
// ori %r11, %r11, 515
.long 0x616b0203
// rldicr %r11, %r11, 32, 31
.long 0x796b07c6
// oris %r11, %r11, 1029
.long 0x656b0405
// ori %r11, %r11, 1543
.long 0x616b0607
// lis %r12, 2057
.long 0x3d800809
// ori %r12, %r12, 2571
.long 0x618c0a0b
// rldicr %r12, %r12, 32, 31
.long 0x798c07c6
// oris %r12, %r12, 5141
.long 0x658c1415
// ori %r12, %r12, 5655
.long 0x618c1617
// mtvsrd 50, %r11
.long 0x7e4b0167
// mtvsrd 33, %r12
.long 0x7c2c0167
// vsldoi %v18, %v0, %v18, 8
.long 0x1240922c
// vsldoi %v18, %v18, %v1, 8
.long 0x12520a2c
// li %r11, 12
.long 0x3960000c
// lwbrx %r8, %r5, %r11
.long 0x7d055c2c
// lxvd2x 42, %r5, %r0
.long 0x7d450699
// vperm %v10, %v10, %v10, %v19
.long 0x114a54eb
// rldicl %r12, %r7, 61, 3
.long 0x78ece8c2
// cmpldi %cr0, %r12, 0
.long 0x282c0000
beq %cr0, 22f
24:
// mtvsrd 43, %r8
.long 0x7d680167
// vperm %v0, %v10, %v11, %v18
.long 0x100a5cab
// addi %r8, %r8, 1
.long 0x39080001
// mtvsrd 43, %r8
.long 0x7d680167
// vperm %v1, %v10, %v11, %v18
.long 0x102a5cab
// addi %r8, %r8, 1
.long 0x39080001
// mtvsrd 43, %r8
.long 0x7d680167
// vperm %v2, %v10, %v11, %v18
.long 0x104a5cab
// addi %r8, %r8, 1
.long 0x39080001
// mtvsrd 43, %r8
.long 0x7d680167
// vperm %v3, %v10, %v11, %v18
.long 0x106a5cab
// addi %r8, %r8, 1
.long 0x39080001
// mtvsrd 43, %r8
.long 0x7d680167
// vperm %v4, %v10, %v11, %v18
.long 0x108a5cab
// addi %r8, %r8, 1
.long 0x39080001
// mtvsrd 43, %r8
.long 0x7d680167
// vperm %v5, %v10, %v11, %v18
.long 0x10aa5cab
// addi %r8, %r8, 1
.long 0x39080001
// mtvsrd 43, %r8
.long 0x7d680167
// vperm %v6, %v10, %v11, %v18
.long 0x10ca5cab
// addi %r8, %r8, 1
.long 0x39080001
// mtvsrd 43, %r8
.long 0x7d680167
// vperm %v7, %v10, %v11, %v18
.long 0x10ea5cab
// addi %r8, %r8, 1
.long 0x39080001
// or %r9, %r3, %r3
.long 0x7c691b78
// lxvd2x 40, %r9, %r0
.long 0x7d090699
// vperm %v8, %v8, %v8, %v19
.long 0x110844eb
// vxor %v0, %v0, %v8
.long 0x100044c4
// vxor %v1, %v1, %v8
.long 0x102144c4
// vxor %v2, %v2, %v8
.long 0x104244c4
// vxor %v3, %v3, %v8
.long 0x106344c4
// vxor %v4, %v4, %v8
.long 0x108444c4
// vxor %v5, %v5, %v8
.long 0x10a544c4
// vxor %v6, %v6, %v8
.long 0x10c644c4
// vxor %v7, %v7, %v8
.long 0x10e744c4
// addi %r9, %r9, 16
.long 0x39290010
// addi %r10, %r4, -1
.long 0x3944ffff
25:
// lxvd2x 40, %r9, %r0
.long 0x7d090699
// vperm %v8, %v8, %v8, %v19
.long 0x110844eb
// vcipher %v0, %v0, %v8
.long 0x10004508
// vcipher %v1, %v1, %v8
.long 0x10214508
// vcipher %v2, %v2, %v8
.long 0x10424508
// vcipher %v3, %v3, %v8
.long 0x10634508
// vcipher %v4, %v4, %v8
.long 0x10844508
// vcipher %v5, %v5, %v8
.long 0x10a54508
// vcipher %v6, %v6, %v8
.long 0x10c64508
// vcipher %v7, %v7, %v8
.long 0x10e74508
// addi %r9, %r9, 16
.long 0x39290010
// addi %r10, %r10, -1
.long 0x394affff
// cmpldi %cr0, %r10, 0
.long 0x282a0000
bne %cr0, 25b
// lxvd2x 40, %r9, %r0
.long 0x7d090699
// vperm %v8, %v8, %v8, %v19
.long 0x110844eb
// vcipherlast %v0, %v0, %v8
.long 0x10004509
// vcipherlast %v1, %v1, %v8
.long 0x10214509
// vcipherlast %v2, %v2, %v8
.long 0x10424509
// vcipherlast %v3, %v3, %v8
.long 0x10634509
// vcipherlast %v4, %v4, %v8
.long 0x10844509
// vcipherlast %v5, %v5, %v8
.long 0x10a54509
// vcipherlast %v6, %v6, %v8
.long 0x10c64509
// vcipherlast %v7, %v7, %v8
.long 0x10e74509
// lxvd2x 41, %r6, %r0
.long 0x7d260699
// vperm %v9, %v9, %v9, %v19
.long 0x11294ceb
// vxor %v0, %v0, %v9
.long 0x10004cc4
// vperm %v0, %v0, %v0, %v19
.long 0x100004eb
// stxvd2x 32, %r6, %r0
.long 0x7c060799
// addi %r6, %r6, 16
.long 0x38c60010
// lxvd2x 41, %r6, %r0
.long 0x7d260699
// vperm %v9, %v9, %v9, %v19
.long 0x11294ceb
// vxor %v1, %v1, %v9
.long 0x10214cc4
// vperm %v1, %v1, %v1, %v19
.long 0x10210ceb
// stxvd2x 33, %r6, %r0
.long 0x7c260799
// addi %r6, %r6, 16
.long 0x38c60010
// lxvd2x 41, %r6, %r0
.long 0x7d260699
// vperm %v9, %v9, %v9, %v19
.long 0x11294ceb
// vxor %v2, %v2, %v9
.long 0x10424cc4
// vperm %v2, %v2, %v2, %v19
.long 0x104214eb
// stxvd2x 34, %r6, %r0
.long 0x7c460799
// addi %r6, %r6, 16
.long 0x38c60010
// lxvd2x 41, %r6, %r0
.long 0x7d260699
// vperm %v9, %v9, %v9, %v19
.long 0x11294ceb
// vxor %v3, %v3, %v9
.long 0x10634cc4
// vperm %v3, %v3, %v3, %v19
.long 0x10631ceb
// stxvd2x 35, %r6, %r0
.long 0x7c660799
// addi %r6, %r6, 16
.long 0x38c60010
// lxvd2x 41, %r6, %r0
.long 0x7d260699
// vperm %v9, %v9, %v9, %v19
.long 0x11294ceb
// vxor %v4, %v4, %v9
.long 0x10844cc4
// vperm %v4, %v4, %v4, %v19
.long 0x108424eb
// stxvd2x 36, %r6, %r0
.long 0x7c860799
// addi %r6, %r6, 16
.long 0x38c60010
// lxvd2x 41, %r6, %r0
.long 0x7d260699
// vperm %v9, %v9, %v9, %v19
.long 0x11294ceb
// vxor %v5, %v5, %v9
.long 0x10a54cc4
// vperm %v5, %v5, %v5, %v19
.long 0x10a52ceb
// stxvd2x 37, %r6, %r0
.long 0x7ca60799
// addi %r6, %r6, 16
.long 0x38c60010
// lxvd2x 41, %r6, %r0
.long 0x7d260699
// vperm %v9, %v9, %v9, %v19
.long 0x11294ceb
// vxor %v6, %v6, %v9
.long 0x10c64cc4
// vperm %v6, %v6, %v6, %v19
.long 0x10c634eb
// stxvd2x 38, %r6, %r0
.long 0x7cc60799
// addi %r6, %r6, 16
.long 0x38c60010
// lxvd2x 41, %r6, %r0
.long 0x7d260699
// vperm %v9, %v9, %v9, %v19
.long 0x11294ceb
// vxor %v7, %v7, %v9
.long 0x10e74cc4
// vperm %v7, %v7, %v7, %v19
.long 0x10e73ceb
// stxvd2x 39, %r6, %r0
.long 0x7ce60799
// addi %r6, %r6, 16
.long 0x38c60010
// addi %r7, %r7, -8
.long 0x38e7fff8
// rldicl %r12, %r7, 61, 3
.long 0x78ece8c2
// cmpldi %cr0, %r12, 0
.long 0x282c0000
bne %cr0, 24b
b 23f
22:
23:
// cmpldi %cr0, %r7, 0
.long 0x28270000
beq %cr0, 26f
28:
// mtvsrd 43, %r8
.long 0x7d680167
// vperm %v0, %v10, %v11, %v18
.long 0x100a5cab
// addi %r8, %r8, 1
.long 0x39080001
// or %r9, %r3, %r3
.long 0x7c691b78
// lxvd2x 40, %r9, %r0
.long 0x7d090699
// vperm %v8, %v8, %v8, %v19
.long 0x110844eb
// vxor %v0, %v0, %v8
.long 0x100044c4
// addi %r9, %r9, 16
.long 0x39290010
// addi %r10, %r4, -1
.long 0x3944ffff
29:
// lxvd2x 40, %r9, %r0
.long 0x7d090699
// vperm %v8, %v8, %v8, %v19
.long 0x110844eb
// vcipher %v0, %v0, %v8
.long 0x10004508
// addi %r9, %r9, 16
.long 0x39290010
// addi %r10, %r10, -1
.long 0x394affff
// cmpldi %cr0, %r10, 0
.long 0x282a0000
bne %cr0, 29b
// lxvd2x 40, %r9, %r0
.long 0x7d090699
// vperm %v8, %v8, %v8, %v19
.long 0x110844eb
// vcipherlast %v0, %v0, %v8
.long 0x10004509
// lxvd2x 41, %r6, %r0
.long 0x7d260699
// vperm %v9, %v9, %v9, %v19
.long 0x11294ceb
// vxor %v0, %v0, %v9
.long 0x10004cc4
// vperm %v0, %v0, %v0, %v19
.long 0x100004eb
// stxvd2x 32, %r6, %r0
.long 0x7c060799
// addi %r6, %r6, 16
.long 0x38c60010
// addi %r7, %r7, -1
.long 0x38e7ffff
// cmpldi %cr0, %r7, 0
.long 0x28270000
bne %cr0, 28b
b 27f
26:
27:
// stwbrx %r8, %r5, %r11
.long 0x7d055d2c
b 21f
20:
21:
// blr
.long 0x4e800020
.globl vg_ghash
.type vg_ghash,@function
vg_ghash:
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 20f
// li %r0, 0
.long 0x38000000
// vxor %v19, %v19, %v19
.long 0x12739cc4
// lis %r8, -15872
.long 0x3d00c200
// ori %r8, %r8, 0
.long 0x61080000
// rldicr %r8, %r8, 32, 31
.long 0x790807c6
// oris %r8, %r8, 0
.long 0x65080000
// ori %r8, %r8, 0
.long 0x61080000
// mtvsrd 33, %r8
.long 0x7c280167
// mtvsrd 39, %r8
.long 0x7ce80167
// vsldoi %v1, %v19, %v1, 8
.long 0x10330a2c
// vsldoi %v1, %v1, %v7, 8
.long 0x10213a2c
// lis %r8, 3854
.long 0x3d000f0e
// ori %r8, %r8, 3340
.long 0x61080d0c
// rldicr %r8, %r8, 32, 31
.long 0x790807c6
// oris %r8, %r8, 2826
.long 0x65080b0a
// ori %r8, %r8, 2312
.long 0x61080908
// lis %r9, 1798
.long 0x3d200706
// ori %r9, %r9, 1284
.long 0x61290504
// rldicr %r9, %r9, 32, 31
.long 0x792907c6
// oris %r9, %r9, 770
.long 0x65290302
// ori %r9, %r9, 256
.long 0x61290100
// mtvsrd 50, %r8
.long 0x7e480167
// mtvsrd 39, %r9
.long 0x7ce90167
// vsldoi %v18, %v19, %v18, 8
.long 0x1253922c
// vsldoi %v18, %v18, %v7, 8
.long 0x12523a2c
// lis %r8, 17920
.long 0x3d004600
// ori %r8, %r8, 0
.long 0x61080000
// rldicr %r8, %r8, 32, 31
.long 0x790807c6
// oris %r8, %r8, 0
.long 0x65080000
// ori %r8, %r8, 0
.long 0x61080000
// li %r9, 3
.long 0x39200003
// mtvsrd 48, %r8
.long 0x7e080167
// mtvsrd 39, %r9
.long 0x7ce90167
// vsldoi %v16, %v19, %v16, 8
.long 0x1213822c
// vsldoi %v16, %v16, %v7, 8
.long 0x12103a2c
// lxvd2x 38, %r3, %r0
.long 0x7cc30699
// vperm %v6, %v6, %v6, %v18
.long 0x10c634ab
// vsldoi %v2, %v6, %v19, 8
.long 0x10469a2c
// vpmsumd %v5, %v2, %v16
.long 0x10a284c8
// vsldoi %v2, %v19, %v6, 8
.long 0x1053322c
// vpmsumd %v3, %v2, %v16
.long 0x106284c8
// vpmsumd %v4, %v6, %v16
.long 0x108684c8
// vsldoi %v7, %v3, %v19, 8
.long 0x10e39a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v3, %v3, %v3, 8
.long 0x10631a2c
// vxor %v4, %v4, %v3
.long 0x10841cc4
// vxor %v4, %v4, %v7
.long 0x10843cc4
// vsldoi %v7, %v4, %v19, 8
.long 0x10e49a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vxor %v5, %v5, %v4
.long 0x10a524c4
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vxor %v16, %v5, %v7
.long 0x12053cc4
// vsldoi %v16, %v16, %v16, 8
.long 0x1210822c
// lxvd2x 32, %r4, %r0
.long 0x7c040699
// vperm %v0, %v0, %v0, %v18
.long 0x100004ab
// rldicl %r10, %r6, 60, 4
.long 0x78cae102
// cmpldi %cr0, %r10, 0
.long 0x282a0000
beq %cr0, 22f
// vsldoi %v6, %v16, %v16, 8
.long 0x10d0822c
// vsldoi %v2, %v6, %v19, 8
.long 0x10469a2c
// vpmsumd %v5, %v2, %v16
.long 0x10a284c8
// vsldoi %v2, %v19, %v6, 8
.long 0x1053322c
// vpmsumd %v3, %v2, %v16
.long 0x106284c8
// vpmsumd %v4, %v6, %v16
.long 0x108684c8
// vsldoi %v7, %v3, %v19, 8
.long 0x10e39a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v3, %v3, %v3, 8
.long 0x10631a2c
// vxor %v4, %v4, %v3
.long 0x10841cc4
// vxor %v4, %v4, %v7
.long 0x10843cc4
// vsldoi %v7, %v4, %v19, 8
.long 0x10e49a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vxor %v5, %v5, %v4
.long 0x10a524c4
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vxor %v8, %v5, %v7
.long 0x11053cc4
// vsldoi %v8, %v8, %v8, 8
.long 0x1108422c
// vsldoi %v6, %v8, %v8, 8
.long 0x10c8422c
// vsldoi %v2, %v6, %v19, 8
.long 0x10469a2c
// vpmsumd %v5, %v2, %v16
.long 0x10a284c8
// vsldoi %v2, %v19, %v6, 8
.long 0x1053322c
// vpmsumd %v3, %v2, %v16
.long 0x106284c8
// vpmsumd %v4, %v6, %v16
.long 0x108684c8
// vsldoi %v7, %v3, %v19, 8
.long 0x10e39a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v3, %v3, %v3, 8
.long 0x10631a2c
// vxor %v4, %v4, %v3
.long 0x10841cc4
// vxor %v4, %v4, %v7
.long 0x10843cc4
// vsldoi %v7, %v4, %v19, 8
.long 0x10e49a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vxor %v5, %v5, %v4
.long 0x10a524c4
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vxor %v9, %v5, %v7
.long 0x11253cc4
// vsldoi %v9, %v9, %v9, 8
.long 0x11294a2c
// vsldoi %v6, %v9, %v9, 8
.long 0x10c94a2c
// vsldoi %v2, %v6, %v19, 8
.long 0x10469a2c
// vpmsumd %v5, %v2, %v16
.long 0x10a284c8
// vsldoi %v2, %v19, %v6, 8
.long 0x1053322c
// vpmsumd %v3, %v2, %v16
.long 0x106284c8
// vpmsumd %v4, %v6, %v16
.long 0x108684c8
// vsldoi %v7, %v3, %v19, 8
.long 0x10e39a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v3, %v3, %v3, 8
.long 0x10631a2c
// vxor %v4, %v4, %v3
.long 0x10841cc4
// vxor %v4, %v4, %v7
.long 0x10843cc4
// vsldoi %v7, %v4, %v19, 8
.long 0x10e49a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vxor %v5, %v5, %v4
.long 0x10a524c4
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vxor %v10, %v5, %v7
.long 0x11453cc4
// vsldoi %v10, %v10, %v10, 8
.long 0x114a522c
// vsldoi %v6, %v10, %v10, 8
.long 0x10ca522c
// vsldoi %v2, %v6, %v19, 8
.long 0x10469a2c
// vpmsumd %v5, %v2, %v16
.long 0x10a284c8
// vsldoi %v2, %v19, %v6, 8
.long 0x1053322c
// vpmsumd %v3, %v2, %v16
.long 0x106284c8
// vpmsumd %v4, %v6, %v16
.long 0x108684c8
// vsldoi %v7, %v3, %v19, 8
.long 0x10e39a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v3, %v3, %v3, 8
.long 0x10631a2c
// vxor %v4, %v4, %v3
.long 0x10841cc4
// vxor %v4, %v4, %v7
.long 0x10843cc4
// vsldoi %v7, %v4, %v19, 8
.long 0x10e49a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vxor %v5, %v5, %v4
.long 0x10a524c4
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vxor %v11, %v5, %v7
.long 0x11653cc4
// vsldoi %v11, %v11, %v11, 8
.long 0x116b5a2c
// vsldoi %v6, %v11, %v11, 8
.long 0x10cb5a2c
// vsldoi %v2, %v6, %v19, 8
.long 0x10469a2c
// vpmsumd %v5, %v2, %v16
.long 0x10a284c8
// vsldoi %v2, %v19, %v6, 8
.long 0x1053322c
// vpmsumd %v3, %v2, %v16
.long 0x106284c8
// vpmsumd %v4, %v6, %v16
.long 0x108684c8
// vsldoi %v7, %v3, %v19, 8
.long 0x10e39a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v3, %v3, %v3, 8
.long 0x10631a2c
// vxor %v4, %v4, %v3
.long 0x10841cc4
// vxor %v4, %v4, %v7
.long 0x10843cc4
// vsldoi %v7, %v4, %v19, 8
.long 0x10e49a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vxor %v5, %v5, %v4
.long 0x10a524c4
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vxor %v12, %v5, %v7
.long 0x11853cc4
// vsldoi %v12, %v12, %v12, 8
.long 0x118c622c
// vsldoi %v6, %v12, %v12, 8
.long 0x10cc622c
// vsldoi %v2, %v6, %v19, 8
.long 0x10469a2c
// vpmsumd %v5, %v2, %v16
.long 0x10a284c8
// vsldoi %v2, %v19, %v6, 8
.long 0x1053322c
// vpmsumd %v3, %v2, %v16
.long 0x106284c8
// vpmsumd %v4, %v6, %v16
.long 0x108684c8
// vsldoi %v7, %v3, %v19, 8
.long 0x10e39a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v3, %v3, %v3, 8
.long 0x10631a2c
// vxor %v4, %v4, %v3
.long 0x10841cc4
// vxor %v4, %v4, %v7
.long 0x10843cc4
// vsldoi %v7, %v4, %v19, 8
.long 0x10e49a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vxor %v5, %v5, %v4
.long 0x10a524c4
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vxor %v13, %v5, %v7
.long 0x11a53cc4
// vsldoi %v13, %v13, %v13, 8
.long 0x11ad6a2c
// vsldoi %v6, %v13, %v13, 8
.long 0x10cd6a2c
// vsldoi %v2, %v6, %v19, 8
.long 0x10469a2c
// vpmsumd %v5, %v2, %v16
.long 0x10a284c8
// vsldoi %v2, %v19, %v6, 8
.long 0x1053322c
// vpmsumd %v3, %v2, %v16
.long 0x106284c8
// vpmsumd %v4, %v6, %v16
.long 0x108684c8
// vsldoi %v7, %v3, %v19, 8
.long 0x10e39a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v3, %v3, %v3, 8
.long 0x10631a2c
// vxor %v4, %v4, %v3
.long 0x10841cc4
// vxor %v4, %v4, %v7
.long 0x10843cc4
// vsldoi %v7, %v4, %v19, 8
.long 0x10e49a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vxor %v5, %v5, %v4
.long 0x10a524c4
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vxor %v14, %v5, %v7
.long 0x11c53cc4
// vsldoi %v14, %v14, %v14, 8
.long 0x11ce722c
// vsldoi %v6, %v13, %v13, 8
.long 0x10cd6a2c
// vsldoi %v7, %v6, %v14, 8
.long 0x10e6722c
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vsldoi %v14, %v14, %v6, 8
.long 0x11ce322c
// vor %v13, %v7, %v7
.long 0x11a73c84
// vsldoi %v6, %v11, %v11, 8
.long 0x10cb5a2c
// vsldoi %v7, %v6, %v12, 8
.long 0x10e6622c
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vsldoi %v12, %v12, %v6, 8
.long 0x118c322c
// vor %v11, %v7, %v7
.long 0x11673c84
// vsldoi %v6, %v9, %v9, 8
.long 0x10c94a2c
// vsldoi %v7, %v6, %v10, 8
.long 0x10e6522c
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vsldoi %v10, %v10, %v6, 8
.long 0x114a322c
// vor %v9, %v7, %v7
.long 0x11273c84
// vsldoi %v6, %v16, %v16, 8
.long 0x10d0822c
// vsldoi %v7, %v6, %v8, 8
.long 0x10e6422c
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vsldoi %v8, %v8, %v6, 8
.long 0x1108322c
// vor %v15, %v7, %v7
.long 0x11e73c84
24:
// lxvd2x 38, %r5, %r0
.long 0x7cc50699
// vperm %v6, %v6, %v6, %v18
.long 0x10c634ab
// addi %r5, %r5, 16
.long 0x38a50010
// vxor %v6, %v6, %v0
.long 0x10c604c4
// lxvd2x 37, %r5, %r0
.long 0x7ca50699
// vperm %v5, %v5, %v5, %v18
.long 0x10a52cab
// addi %r5, %r5, 16
.long 0x38a50010
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vsldoi %v2, %v6, %v5, 8
.long 0x10462a2c
// vsldoi %v7, %v5, %v6, 8
.long 0x10e5322c
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vpmsumd %v5, %v2, %v13
.long 0x10a26cc8
// vpmsumd %v3, %v7, %v14
.long 0x106774c8
// vpmsumd %v4, %v2, %v14
.long 0x108274c8
// vpmsumd %v2, %v7, %v13
.long 0x10476cc8
// vxor %v4, %v4, %v2
.long 0x108414c4
// vor %v0, %v3, %v3
.long 0x10031c84
// vor %v16, %v4, %v4
.long 0x12042484
// vor %v17, %v5, %v5
.long 0x12252c84
// lxvd2x 38, %r5, %r0
.long 0x7cc50699
// vperm %v6, %v6, %v6, %v18
.long 0x10c634ab
// addi %r5, %r5, 16
.long 0x38a50010
// lxvd2x 37, %r5, %r0
.long 0x7ca50699
// vperm %v5, %v5, %v5, %v18
.long 0x10a52cab
// addi %r5, %r5, 16
.long 0x38a50010
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vsldoi %v2, %v6, %v5, 8
.long 0x10462a2c
// vsldoi %v7, %v5, %v6, 8
.long 0x10e5322c
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vpmsumd %v5, %v2, %v11
.long 0x10a25cc8
// vpmsumd %v3, %v7, %v12
.long 0x106764c8
// vpmsumd %v4, %v2, %v12
.long 0x108264c8
// vpmsumd %v2, %v7, %v11
.long 0x10475cc8
// vxor %v4, %v4, %v2
.long 0x108414c4
// vxor %v0, %v0, %v3
.long 0x10001cc4
// vxor %v16, %v16, %v4
.long 0x121024c4
// vxor %v17, %v17, %v5
.long 0x12312cc4
// lxvd2x 38, %r5, %r0
.long 0x7cc50699
// vperm %v6, %v6, %v6, %v18
.long 0x10c634ab
// addi %r5, %r5, 16
.long 0x38a50010
// lxvd2x 37, %r5, %r0
.long 0x7ca50699
// vperm %v5, %v5, %v5, %v18
.long 0x10a52cab
// addi %r5, %r5, 16
.long 0x38a50010
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vsldoi %v2, %v6, %v5, 8
.long 0x10462a2c
// vsldoi %v7, %v5, %v6, 8
.long 0x10e5322c
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vpmsumd %v5, %v2, %v9
.long 0x10a24cc8
// vpmsumd %v3, %v7, %v10
.long 0x106754c8
// vpmsumd %v4, %v2, %v10
.long 0x108254c8
// vpmsumd %v2, %v7, %v9
.long 0x10474cc8
// vxor %v4, %v4, %v2
.long 0x108414c4
// vxor %v0, %v0, %v3
.long 0x10001cc4
// vxor %v16, %v16, %v4
.long 0x121024c4
// vxor %v17, %v17, %v5
.long 0x12312cc4
// lxvd2x 38, %r5, %r0
.long 0x7cc50699
// vperm %v6, %v6, %v6, %v18
.long 0x10c634ab
// addi %r5, %r5, 16
.long 0x38a50010
// lxvd2x 37, %r5, %r0
.long 0x7ca50699
// vperm %v5, %v5, %v5, %v18
.long 0x10a52cab
// addi %r5, %r5, 16
.long 0x38a50010
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vsldoi %v2, %v6, %v5, 8
.long 0x10462a2c
// vsldoi %v7, %v5, %v6, 8
.long 0x10e5322c
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vpmsumd %v5, %v2, %v15
.long 0x10a27cc8
// vpmsumd %v3, %v7, %v8
.long 0x106744c8
// vpmsumd %v4, %v2, %v8
.long 0x108244c8
// vpmsumd %v2, %v7, %v15
.long 0x10477cc8
// vxor %v4, %v4, %v2
.long 0x108414c4
// vxor %v3, %v3, %v0
.long 0x106304c4
// vxor %v4, %v4, %v16
.long 0x108484c4
// vxor %v5, %v5, %v17
.long 0x10a58cc4
// vsldoi %v7, %v3, %v19, 8
.long 0x10e39a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v3, %v3, %v3, 8
.long 0x10631a2c
// vxor %v4, %v4, %v3
.long 0x10841cc4
// vxor %v4, %v4, %v7
.long 0x10843cc4
// vsldoi %v7, %v4, %v19, 8
.long 0x10e49a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vxor %v5, %v5, %v4
.long 0x10a524c4
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vxor %v0, %v5, %v7
.long 0x10053cc4
// addi %r6, %r6, -8
.long 0x38c6fff8
// rldicl %r10, %r6, 61, 3
.long 0x78cae8c2
// cmpldi %cr0, %r10, 0
.long 0x282a0000
bne %cr0, 24b
// vsldoi %v6, %v8, %v8, 8
.long 0x10c8422c
// vsldoi %v16, %v15, %v6, 8
.long 0x120f322c
// cmpldi %cr0, %r6, 0
.long 0x28260000
beq %cr0, 25f
27:
// lxvd2x 38, %r5, %r0
.long 0x7cc50699
// vperm %v6, %v6, %v6, %v18
.long 0x10c634ab
// vxor %v6, %v6, %v0
.long 0x10c604c4
// vsldoi %v2, %v6, %v19, 8
.long 0x10469a2c
// vpmsumd %v5, %v2, %v16
.long 0x10a284c8
// vsldoi %v2, %v19, %v6, 8
.long 0x1053322c
// vpmsumd %v3, %v2, %v16
.long 0x106284c8
// vpmsumd %v4, %v6, %v16
.long 0x108684c8
// vsldoi %v7, %v3, %v19, 8
.long 0x10e39a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v3, %v3, %v3, 8
.long 0x10631a2c
// vxor %v4, %v4, %v3
.long 0x10841cc4
// vxor %v4, %v4, %v7
.long 0x10843cc4
// vsldoi %v7, %v4, %v19, 8
.long 0x10e49a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vxor %v5, %v5, %v4
.long 0x10a524c4
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vxor %v0, %v5, %v7
.long 0x10053cc4
// addi %r5, %r5, 16
.long 0x38a50010
// addi %r6, %r6, -1
.long 0x38c6ffff
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 27b
b 26f
25:
26:
// vperm %v7, %v0, %v0, %v18
.long 0x10e004ab
// stxvd2x 39, %r4, %r0
.long 0x7ce40799
b 23f
22:
28:
// lxvd2x 38, %r5, %r0
.long 0x7cc50699
// vperm %v6, %v6, %v6, %v18
.long 0x10c634ab
// vxor %v6, %v6, %v0
.long 0x10c604c4
// vsldoi %v2, %v6, %v19, 8
.long 0x10469a2c
// vpmsumd %v5, %v2, %v16
.long 0x10a284c8
// vsldoi %v2, %v19, %v6, 8
.long 0x1053322c
// vpmsumd %v3, %v2, %v16
.long 0x106284c8
// vpmsumd %v4, %v6, %v16
.long 0x108684c8
// vsldoi %v7, %v3, %v19, 8
.long 0x10e39a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v3, %v3, %v3, 8
.long 0x10631a2c
// vxor %v4, %v4, %v3
.long 0x10841cc4
// vxor %v4, %v4, %v7
.long 0x10843cc4
// vsldoi %v7, %v4, %v19, 8
.long 0x10e49a2c
// vpmsumd %v7, %v7, %v1
.long 0x10e70cc8
// vsldoi %v5, %v5, %v5, 8
.long 0x10a52a2c
// vxor %v5, %v5, %v4
.long 0x10a524c4
// vsldoi %v7, %v7, %v7, 8
.long 0x10e73a2c
// vxor %v0, %v5, %v7
.long 0x10053cc4
// addi %r5, %r5, 16
.long 0x38a50010
// addi %r6, %r6, -1
.long 0x38c6ffff
// cmpldi %cr0, %r6, 0
.long 0x28260000
bne %cr0, 28b
// vperm %v7, %v0, %v0, %v18
.long 0x10e004ab
// stxvd2x 39, %r4, %r0
.long 0x7ce40799
23:
b 21f
20:
21:
// blr
.long 0x4e800020
