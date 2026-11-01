.text
.abiversion 2
.globl gcm_staged8_unroll
.type gcm_staged8_unroll,@function
gcm_staged8_unroll:
cmpldi %cr0, %r7, 0
beq %cr0, 20f
std %r14, 0(%r10)
std %r15, 8(%r10)
std %r16, 16(%r10)
std %r18, 24(%r10)
std %r19, 32(%r10)
std %r20, 40(%r10)
std %r21, 48(%r10)
std %r22, 56(%r10)
std %r23, 64(%r10)
std %r24, 72(%r10)
std %r25, 80(%r10)
or %r16, %r10, %r10
addi %r16, %r16, 128
or %r14, %r9, %r9
or %r15, %r6, %r6
li %r0, 0
vxor %v0, %v0, %v0
lis %r11, 1798
ori %r11, %r11, 1284
rldicr %r11, %r11, 32, 31
oris %r11, %r11, 770
ori %r11, %r11, 256
lis %r12, 3854
ori %r12, %r12, 3340
rldicr %r12, %r12, 32, 31
oris %r12, %r12, 2826
ori %r12, %r12, 2312
mtvsrd 51, %r11
mtvsrd 33, %r12
vsldoi %v19, %v0, %v19, 8
vsldoi %v19, %v19, %v1, 8
li %r20, 16
li %r21, 48
li %r22, 64
li %r23, 32
addi %r24, %r16, 256
li %r25, 96
stxvd2x 32, %r16, %r0
stxvd2x 51, %r16, %r25
lis %r11, 0
ori %r11, %r11, 0
rldicr %r11, %r11, 32, 31
oris %r11, %r11, 0
ori %r11, %r11, 0
lis %r12, 0
ori %r12, %r12, 0
rldicr %r12, %r12, 32, 31
oris %r12, %r12, 0
ori %r12, %r12, 1
mtvsrd 49, %r11
mtvsrd 33, %r12
vsldoi %v17, %v0, %v17, 8
vsldoi %v17, %v17, %v1, 8
stxvd2x 49, %r16, %r20
lis %r11, -15872
ori %r11, %r11, 0
rldicr %r11, %r11, 32, 31
oris %r11, %r11, 0
ori %r11, %r11, 0
lis %r12, -15872
ori %r12, %r12, 0
rldicr %r12, %r12, 32, 31
oris %r12, %r12, 0
ori %r12, %r12, 0
mtvsrd 45, %r11
mtvsrd 33, %r12
vsldoi %v13, %v0, %v13, 8
vsldoi %v13, %v13, %v1, 8
stxvd2x 45, %r16, %r23
lis %r11, 17920
ori %r11, %r11, 0
rldicr %r11, %r11, 32, 31
oris %r11, %r11, 0
ori %r11, %r11, 0
lis %r12, 0
ori %r12, %r12, 0
rldicr %r12, %r12, 32, 31
oris %r12, %r12, 0
ori %r12, %r12, 3
mtvsrd 43, %r11
mtvsrd 33, %r12
vsldoi %v11, %v0, %v11, 8
vsldoi %v11, %v11, %v1, 8
lxvd2x 41, %r8, %r0
vperm %v9, %v9, %v9, %v19
vsldoi %v9, %v9, %v9, 8
vsldoi %v17, %v9, %v0, 8
vpmsumd %v16, %v17, %v11
vsldoi %v17, %v0, %v9, 8
vpmsumd %v14, %v17, %v11
vpmsumd %v15, %v9, %v11
vsldoi %v18, %v14, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v14, %v14, %v14, 8
vxor %v15, %v15, %v14
vxor %v15, %v15, %v18
vsldoi %v18, %v15, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v16, %v16, %v16, 8
vxor %v16, %v16, %v15
vsldoi %v18, %v18, %v18, 8
vxor %v11, %v16, %v18
vsldoi %v11, %v11, %v11, 8
li %r11, 80
stxvd2x 43, %r16, %r11
vsldoi %v9, %v11, %v11, 8
vsldoi %v17, %v9, %v0, 8
vpmsumd %v16, %v17, %v11
vsldoi %v17, %v0, %v9, 8
vpmsumd %v14, %v17, %v11
vpmsumd %v15, %v9, %v11
vsldoi %v18, %v14, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v14, %v14, %v14, 8
vxor %v15, %v15, %v14
vxor %v15, %v15, %v18
vsldoi %v18, %v15, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v16, %v16, %v16, 8
vxor %v16, %v16, %v15
vsldoi %v18, %v18, %v18, 8
vxor %v12, %v16, %v18
vsldoi %v12, %v12, %v12, 8
vsldoi %v9, %v11, %v11, 8
vsldoi %v18, %v9, %v12, 8
vsldoi %v18, %v18, %v18, 8
vsldoi %v11, %v12, %v9, 8
vor %v12, %v18, %v18
stxvd2x 43, %r16, %r21
stxvd2x 44, %r16, %r22
lxvd2x 42, %r14, %r0
vperm %v10, %v10, %v10, %v19
ldbrx %r18, %r5, %r0
li %r11, 8
lwbrx %r19, %r5, %r11
rldicr %r19, %r19, 32, 31
li %r11, 12
lwbrx %r8, %r5, %r11
or %r9, %r3, %r3
li %r11, 80
lxvd2x 43, %r16, %r11
vor %v12, %v11, %v11
li %r11, 256
stxvd2x 43, %r16, %r11
vsldoi %v9, %v12, %v12, 8
vsldoi %v17, %v9, %v0, 8
vpmsumd %v16, %v17, %v11
vsldoi %v17, %v0, %v9, 8
vpmsumd %v14, %v17, %v11
vpmsumd %v15, %v9, %v11
vsldoi %v18, %v14, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v14, %v14, %v14, 8
vxor %v15, %v15, %v14
vxor %v15, %v15, %v18
vsldoi %v18, %v15, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v16, %v16, %v16, 8
vxor %v16, %v16, %v15
vsldoi %v18, %v18, %v18, 8
vxor %v12, %v16, %v18
vsldoi %v12, %v12, %v12, 8
li %r11, 272
stxvd2x 44, %r16, %r11
vsldoi %v9, %v12, %v12, 8
vsldoi %v17, %v9, %v0, 8
vpmsumd %v16, %v17, %v11
vsldoi %v17, %v0, %v9, 8
vpmsumd %v14, %v17, %v11
vpmsumd %v15, %v9, %v11
vsldoi %v18, %v14, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v14, %v14, %v14, 8
vxor %v15, %v15, %v14
vxor %v15, %v15, %v18
vsldoi %v18, %v15, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v16, %v16, %v16, 8
vxor %v16, %v16, %v15
vsldoi %v18, %v18, %v18, 8
vxor %v12, %v16, %v18
vsldoi %v12, %v12, %v12, 8
li %r11, 288
stxvd2x 44, %r16, %r11
vsldoi %v9, %v12, %v12, 8
vsldoi %v17, %v9, %v0, 8
vpmsumd %v16, %v17, %v11
vsldoi %v17, %v0, %v9, 8
vpmsumd %v14, %v17, %v11
vpmsumd %v15, %v9, %v11
vsldoi %v18, %v14, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v14, %v14, %v14, 8
vxor %v15, %v15, %v14
vxor %v15, %v15, %v18
vsldoi %v18, %v15, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v16, %v16, %v16, 8
vxor %v16, %v16, %v15
vsldoi %v18, %v18, %v18, 8
vxor %v12, %v16, %v18
vsldoi %v12, %v12, %v12, 8
li %r11, 304
stxvd2x 44, %r16, %r11
vsldoi %v9, %v12, %v12, 8
vsldoi %v17, %v9, %v0, 8
vpmsumd %v16, %v17, %v11
vsldoi %v17, %v0, %v9, 8
vpmsumd %v14, %v17, %v11
vpmsumd %v15, %v9, %v11
vsldoi %v18, %v14, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v14, %v14, %v14, 8
vxor %v15, %v15, %v14
vxor %v15, %v15, %v18
vsldoi %v18, %v15, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v16, %v16, %v16, 8
vxor %v16, %v16, %v15
vsldoi %v18, %v18, %v18, 8
vxor %v12, %v16, %v18
vsldoi %v12, %v12, %v12, 8
li %r11, 320
stxvd2x 44, %r16, %r11
vsldoi %v9, %v12, %v12, 8
vsldoi %v17, %v9, %v0, 8
vpmsumd %v16, %v17, %v11
vsldoi %v17, %v0, %v9, 8
vpmsumd %v14, %v17, %v11
vpmsumd %v15, %v9, %v11
vsldoi %v18, %v14, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v14, %v14, %v14, 8
vxor %v15, %v15, %v14
vxor %v15, %v15, %v18
vsldoi %v18, %v15, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v16, %v16, %v16, 8
vxor %v16, %v16, %v15
vsldoi %v18, %v18, %v18, 8
vxor %v12, %v16, %v18
vsldoi %v12, %v12, %v12, 8
li %r11, 336
stxvd2x 44, %r16, %r11
vsldoi %v9, %v12, %v12, 8
vsldoi %v17, %v9, %v0, 8
vpmsumd %v16, %v17, %v11
vsldoi %v17, %v0, %v9, 8
vpmsumd %v14, %v17, %v11
vpmsumd %v15, %v9, %v11
vsldoi %v18, %v14, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v14, %v14, %v14, 8
vxor %v15, %v15, %v14
vxor %v15, %v15, %v18
vsldoi %v18, %v15, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v16, %v16, %v16, 8
vxor %v16, %v16, %v15
vsldoi %v18, %v18, %v18, 8
vxor %v12, %v16, %v18
vsldoi %v12, %v12, %v12, 8
li %r11, 352
stxvd2x 44, %r16, %r11
vsldoi %v9, %v12, %v12, 8
vsldoi %v17, %v9, %v0, 8
vpmsumd %v16, %v17, %v11
vsldoi %v17, %v0, %v9, 8
vpmsumd %v14, %v17, %v11
vpmsumd %v15, %v9, %v11
vsldoi %v18, %v14, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v14, %v14, %v14, 8
vxor %v15, %v15, %v14
vxor %v15, %v15, %v18
vsldoi %v18, %v15, %v0, 8
vpmsumd %v18, %v18, %v13
vsldoi %v16, %v16, %v16, 8
vxor %v16, %v16, %v15
vsldoi %v18, %v18, %v18, 8
vxor %v12, %v16, %v18
vsldoi %v12, %v12, %v12, 8
li %r11, 368
stxvd2x 44, %r16, %r11
li %r11, 368
lxvd2x 43, %r16, %r11
li %r11, 352
lxvd2x 44, %r16, %r11
vsldoi %v9, %v12, %v12, 8
vsldoi %v18, %v9, %v11, 8
vsldoi %v18, %v18, %v18, 8
vsldoi %v11, %v11, %v9, 8
li %r11, 128
stxvd2x 43, %r16, %r11
li %r11, 144
stxvd2x 50, %r16, %r11
li %r11, 336
lxvd2x 43, %r16, %r11
li %r11, 320
lxvd2x 44, %r16, %r11
vsldoi %v9, %v12, %v12, 8
vsldoi %v18, %v9, %v11, 8
vsldoi %v18, %v18, %v18, 8
vsldoi %v11, %v11, %v9, 8
li %r11, 160
stxvd2x 43, %r16, %r11
li %r11, 176
stxvd2x 50, %r16, %r11
li %r11, 304
lxvd2x 43, %r16, %r11
li %r11, 288
lxvd2x 44, %r16, %r11
vsldoi %v9, %v12, %v12, 8
vsldoi %v18, %v9, %v11, 8
vsldoi %v18, %v18, %v18, 8
vsldoi %v11, %v11, %v9, 8
li %r11, 192
stxvd2x 43, %r16, %r11
li %r11, 208
stxvd2x 50, %r16, %r11
li %r11, 272
lxvd2x 43, %r16, %r11
li %r11, 256
lxvd2x 44, %r16, %r11
vsldoi %v9, %v12, %v12, 8
vsldoi %v18, %v9, %v11, 8
vsldoi %v18, %v18, %v18, 8
vsldoi %v11, %v11, %v9, 8
li %r11, 224
stxvd2x 43, %r16, %r11
li %r11, 240
stxvd2x 50, %r16, %r11
or %r11, %r24, %r24
addi %r12, %r4, 1
22:
lxvd2x 40, %r9, %r0
vperm %v8, %v8, %v8, %v19
stxvd2x 40, %r11, %r0
addi %r9, %r9, 16
addi %r11, %r11, 16
addi %r12, %r12, -1
cmpldi %cr0, %r12, 0
bne %cr0, 22b
or %r3, %r24, %r24
li %r23, 64
li %r24, 80
23:
rldicr %r11, %r8, 32, 31
rldicl %r11, %r11, 32, 32
or %r11, %r19, %r11
lxvd2x 49, %r16, %r0
mtvsrd 41, %r18
mtvsrd 50, %r11
vsldoi %v9, %v17, %v9, 8
vsldoi %v9, %v9, %v18, 8
lxvd2x 49, %r16, %r20
vadduwm %v18, %v17, %v17
vor %v0, %v9, %v9
vadduwm %v1, %v9, %v17
vadduwm %v2, %v0, %v18
vadduwm %v3, %v1, %v18
vadduwm %v4, %v2, %v18
vadduwm %v5, %v3, %v18
vadduwm %v6, %v4, %v18
vadduwm %v7, %v5, %v18
addi %r8, %r8, 8
lxvd2x 40, %r3, %r0
vxor %v0, %v0, %v8
vxor %v1, %v1, %v8
vxor %v2, %v2, %v8
vxor %v3, %v3, %v8
vxor %v4, %v4, %v8
vxor %v5, %v5, %v8
vxor %v6, %v6, %v8
vxor %v7, %v7, %v8
lxvd2x 40, %r3, %r20
vcipher %v0, %v0, %v8
vcipher %v1, %v1, %v8
vcipher %v2, %v2, %v8
vcipher %v3, %v3, %v8
vcipher %v4, %v4, %v8
vcipher %v5, %v5, %v8
vcipher %v6, %v6, %v8
vcipher %v7, %v7, %v8
li %r21, 32
lxvd2x 40, %r3, %r21
vcipher %v0, %v0, %v8
vcipher %v1, %v1, %v8
vcipher %v2, %v2, %v8
vcipher %v3, %v3, %v8
vcipher %v4, %v4, %v8
vcipher %v5, %v5, %v8
vcipher %v6, %v6, %v8
vcipher %v7, %v7, %v8
li %r22, 48
lxvd2x 40, %r3, %r22
vcipher %v0, %v0, %v8
vcipher %v1, %v1, %v8
vcipher %v2, %v2, %v8
vcipher %v3, %v3, %v8
vcipher %v4, %v4, %v8
vcipher %v5, %v5, %v8
vcipher %v6, %v6, %v8
vcipher %v7, %v7, %v8
lxvd2x 40, %r3, %r23
vcipher %v0, %v0, %v8
vcipher %v1, %v1, %v8
vcipher %v2, %v2, %v8
vcipher %v3, %v3, %v8
vcipher %v4, %v4, %v8
vcipher %v5, %v5, %v8
vcipher %v6, %v6, %v8
vcipher %v7, %v7, %v8
lxvd2x 40, %r3, %r24
vcipher %v0, %v0, %v8
vcipher %v1, %v1, %v8
vcipher %v2, %v2, %v8
vcipher %v3, %v3, %v8
vcipher %v4, %v4, %v8
vcipher %v5, %v5, %v8
vcipher %v6, %v6, %v8
vcipher %v7, %v7, %v8
lxvd2x 40, %r3, %r25
vcipher %v0, %v0, %v8
vcipher %v1, %v1, %v8
vcipher %v2, %v2, %v8
vcipher %v3, %v3, %v8
vcipher %v4, %v4, %v8
vcipher %v5, %v5, %v8
vcipher %v6, %v6, %v8
vcipher %v7, %v7, %v8
li %r11, 112
lxvd2x 40, %r3, %r11
vcipher %v0, %v0, %v8
vcipher %v1, %v1, %v8
vcipher %v2, %v2, %v8
vcipher %v3, %v3, %v8
vcipher %v4, %v4, %v8
vcipher %v5, %v5, %v8
vcipher %v6, %v6, %v8
vcipher %v7, %v7, %v8
li %r12, 128
lxvd2x 40, %r3, %r12
vcipher %v0, %v0, %v8
vcipher %v1, %v1, %v8
vcipher %v2, %v2, %v8
vcipher %v3, %v3, %v8
vcipher %v4, %v4, %v8
vcipher %v5, %v5, %v8
vcipher %v6, %v6, %v8
vcipher %v7, %v7, %v8
addi %r9, %r3, 144
addi %r10, %r4, -9
24:
lxvd2x 40, %r9, %r0
vcipher %v0, %v0, %v8
vcipher %v1, %v1, %v8
vcipher %v2, %v2, %v8
vcipher %v3, %v3, %v8
vcipher %v4, %v4, %v8
vcipher %v5, %v5, %v8
vcipher %v6, %v6, %v8
vcipher %v7, %v7, %v8
addi %r9, %r9, 16
addi %r10, %r10, -1
cmpldi %cr0, %r10, 0
bne %cr0, 24b
lxvd2x 40, %r9, %r0
vcipherlast %v0, %v0, %v8
vcipherlast %v1, %v1, %v8
vcipherlast %v2, %v2, %v8
vcipherlast %v3, %v3, %v8
vcipherlast %v4, %v4, %v8
vcipherlast %v5, %v5, %v8
vcipherlast %v6, %v6, %v8
vcipherlast %v7, %v7, %v8
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v0, %v0, %v9
vperm %v9, %v0, %v0, %v19
stxvd2x 41, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v1, %v1, %v9
vperm %v9, %v1, %v1, %v19
stxvd2x 41, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v2, %v2, %v9
vperm %v9, %v2, %v2, %v19
stxvd2x 41, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v3, %v3, %v9
vperm %v9, %v3, %v3, %v19
stxvd2x 41, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v4, %v4, %v9
vperm %v9, %v4, %v4, %v19
stxvd2x 41, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v5, %v5, %v9
vperm %v9, %v5, %v5, %v19
stxvd2x 41, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v6, %v6, %v9
vperm %v9, %v6, %v6, %v19
stxvd2x 41, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v7, %v7, %v9
vperm %v9, %v7, %v7, %v19
stxvd2x 41, %r6, %r0
addi %r6, %r6, 16
addi %r7, %r7, -8
li %r21, 128
li %r22, 144
vxor %v0, %v0, %v10
lxvd2x 40, %r16, %r21
lxvd2x 41, %r16, %r22
addi %r21, %r21, 32
addi %r22, %r22, 32
vsldoi %v16, %v1, %v1, 8
vsldoi %v18, %v0, %v16, 8
vsldoi %v17, %v16, %v0, 8
vsldoi %v17, %v17, %v17, 8
vpmsumd %v16, %v17, %v9
vpmsumd %v14, %v18, %v8
vpmsumd %v15, %v17, %v8
vpmsumd %v17, %v18, %v9
vxor %v15, %v15, %v17
vor %v10, %v14, %v14
vor %v11, %v15, %v15
vor %v12, %v16, %v16
lxvd2x 40, %r16, %r21
lxvd2x 41, %r16, %r22
addi %r21, %r21, 32
addi %r22, %r22, 32
vsldoi %v16, %v3, %v3, 8
vsldoi %v18, %v2, %v16, 8
vsldoi %v17, %v16, %v2, 8
vsldoi %v17, %v17, %v17, 8
vpmsumd %v16, %v17, %v9
vpmsumd %v14, %v18, %v8
vpmsumd %v15, %v17, %v8
vpmsumd %v17, %v18, %v9
vxor %v15, %v15, %v17
vxor %v10, %v10, %v14
vxor %v11, %v11, %v15
vxor %v12, %v12, %v16
lxvd2x 40, %r16, %r21
lxvd2x 41, %r16, %r22
addi %r21, %r21, 32
addi %r22, %r22, 32
vsldoi %v16, %v5, %v5, 8
vsldoi %v18, %v4, %v16, 8
vsldoi %v17, %v16, %v4, 8
vsldoi %v17, %v17, %v17, 8
vpmsumd %v16, %v17, %v9
vpmsumd %v14, %v18, %v8
vpmsumd %v15, %v17, %v8
vpmsumd %v17, %v18, %v9
vxor %v15, %v15, %v17
vxor %v10, %v10, %v14
vxor %v11, %v11, %v15
vxor %v12, %v12, %v16
lxvd2x 40, %r16, %r21
lxvd2x 41, %r16, %r22
addi %r21, %r21, 32
addi %r22, %r22, 32
vsldoi %v16, %v7, %v7, 8
vsldoi %v18, %v6, %v16, 8
vsldoi %v17, %v16, %v6, 8
vsldoi %v17, %v17, %v17, 8
vpmsumd %v16, %v17, %v9
vpmsumd %v14, %v18, %v8
vpmsumd %v15, %v17, %v8
vpmsumd %v17, %v18, %v9
vxor %v15, %v15, %v17
vxor %v14, %v14, %v10
vxor %v15, %v15, %v11
vxor %v16, %v16, %v12
vxor %v17, %v17, %v17
vsldoi %v18, %v14, %v17, 8
vpmsumd %v18, %v18, %v13
vsldoi %v14, %v14, %v14, 8
vxor %v15, %v15, %v14
vxor %v15, %v15, %v18
vsldoi %v18, %v15, %v17, 8
vpmsumd %v18, %v18, %v13
vsldoi %v16, %v16, %v16, 8
vxor %v16, %v16, %v15
vsldoi %v18, %v18, %v18, 8
vxor %v10, %v16, %v18
vsldoi %v10, %v10, %v10, 8
cmpldi %cr0, %r7, 0
bne %cr0, 23b
li %r11, 12
stwbrx %r8, %r5, %r11
lxvd2x 40, %r16, %r25
vperm %v10, %v10, %v10, %v8
stxvd2x 42, %r14, %r0
addi %r12, %r16, -128
ld %r14, 0(%r12)
ld %r15, 8(%r12)
ld %r16, 16(%r12)
ld %r18, 24(%r12)
ld %r19, 32(%r12)
ld %r20, 40(%r12)
ld %r21, 48(%r12)
ld %r22, 56(%r12)
ld %r23, 64(%r12)
ld %r24, 72(%r12)
ld %r25, 80(%r12)
b 21f
20:
21:
blr
