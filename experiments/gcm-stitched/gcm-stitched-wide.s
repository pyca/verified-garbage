.text
.abiversion 2
.globl gcm_stitched16
.type gcm_stitched16,@function
gcm_stitched16:
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
li %r11, 640
stxvd2x 52, %r16, %r11
li %r11, 656
stxvd2x 53, %r16, %r11
li %r11, 672
stxvd2x 54, %r16, %r11
li %r11, 688
stxvd2x 55, %r16, %r11
li %r11, 704
stxvd2x 56, %r16, %r11
li %r11, 720
stxvd2x 57, %r16, %r11
li %r11, 736
stxvd2x 58, %r16, %r11
li %r11, 752
stxvd2x 59, %r16, %r11
li %r11, 768
stxvd2x 60, %r16, %r11
li %r11, 784
stxvd2x 61, %r16, %r11
li %r11, 800
stxvd2x 62, %r16, %r11
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
vor %v29, %v19, %v19
vxor %v30, %v30, %v30
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
vadduwm %v20, %v6, %v18
vadduwm %v21, %v7, %v18
vadduwm %v22, %v20, %v18
vadduwm %v23, %v21, %v18
vadduwm %v24, %v22, %v18
vadduwm %v25, %v23, %v18
vadduwm %v26, %v24, %v18
vadduwm %v27, %v25, %v18
addi %r8, %r8, 16
or %r9, %r3, %r3
lxvd2x 40, %r9, %r0
vxor %v0, %v0, %v8
vxor %v1, %v1, %v8
vxor %v2, %v2, %v8
vxor %v3, %v3, %v8
vxor %v4, %v4, %v8
vxor %v5, %v5, %v8
vxor %v6, %v6, %v8
vxor %v7, %v7, %v8
vxor %v20, %v20, %v8
vxor %v21, %v21, %v8
vxor %v22, %v22, %v8
vxor %v23, %v23, %v8
vxor %v24, %v24, %v8
vxor %v25, %v25, %v8
vxor %v26, %v26, %v8
vxor %v27, %v27, %v8
addi %r9, %r9, 16
addi %r10, %r4, -1
23:
lxvd2x 40, %r9, %r0
vcipher %v0, %v0, %v8
vcipher %v1, %v1, %v8
vcipher %v2, %v2, %v8
vcipher %v3, %v3, %v8
vcipher %v4, %v4, %v8
vcipher %v5, %v5, %v8
vcipher %v6, %v6, %v8
vcipher %v7, %v7, %v8
vcipher %v20, %v20, %v8
vcipher %v21, %v21, %v8
vcipher %v22, %v22, %v8
vcipher %v23, %v23, %v8
vcipher %v24, %v24, %v8
vcipher %v25, %v25, %v8
vcipher %v26, %v26, %v8
vcipher %v27, %v27, %v8
addi %r9, %r9, 16
addi %r10, %r10, -1
cmpldi %cr0, %r10, 0
bne %cr0, 23b
lxvd2x 40, %r9, %r0
vcipherlast %v0, %v0, %v8
vcipherlast %v1, %v1, %v8
vcipherlast %v2, %v2, %v8
vcipherlast %v3, %v3, %v8
vcipherlast %v4, %v4, %v8
vcipherlast %v5, %v5, %v8
vcipherlast %v6, %v6, %v8
vcipherlast %v7, %v7, %v8
vcipherlast %v20, %v20, %v8
vcipherlast %v21, %v21, %v8
vcipherlast %v22, %v22, %v8
vcipherlast %v23, %v23, %v8
vcipherlast %v24, %v24, %v8
vcipherlast %v25, %v25, %v8
vcipherlast %v26, %v26, %v8
vcipherlast %v27, %v27, %v8
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v0, %v0, %v9
vperm %v0, %v0, %v0, %v29
stxvd2x 32, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v1, %v1, %v9
vperm %v1, %v1, %v1, %v29
stxvd2x 33, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v2, %v2, %v9
vperm %v2, %v2, %v2, %v29
stxvd2x 34, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v3, %v3, %v9
vperm %v3, %v3, %v3, %v29
stxvd2x 35, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v4, %v4, %v9
vperm %v4, %v4, %v4, %v29
stxvd2x 36, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v5, %v5, %v9
vperm %v5, %v5, %v5, %v29
stxvd2x 37, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v6, %v6, %v9
vperm %v6, %v6, %v6, %v29
stxvd2x 38, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v7, %v7, %v9
vperm %v7, %v7, %v7, %v29
stxvd2x 39, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v20, %v20, %v9
vperm %v20, %v20, %v20, %v29
stxvd2x 52, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v21, %v21, %v9
vperm %v21, %v21, %v21, %v29
stxvd2x 53, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v22, %v22, %v9
vperm %v22, %v22, %v22, %v29
stxvd2x 54, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v23, %v23, %v9
vperm %v23, %v23, %v23, %v29
stxvd2x 55, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v24, %v24, %v9
vperm %v24, %v24, %v24, %v29
stxvd2x 56, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v25, %v25, %v9
vperm %v25, %v25, %v25, %v29
stxvd2x 57, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v26, %v26, %v9
vperm %v26, %v26, %v26, %v29
stxvd2x 58, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v27, %v27, %v9
vperm %v27, %v27, %v27, %v29
stxvd2x 59, %r6, %r0
addi %r6, %r6, 16
addi %r7, %r7, -16
cmpldi %cr0, %r7, 0
beq %cr0, 24f
26:
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
vadduwm %v20, %v6, %v18
vadduwm %v21, %v7, %v18
vadduwm %v22, %v20, %v18
vadduwm %v23, %v21, %v18
vadduwm %v24, %v22, %v18
vadduwm %v25, %v23, %v18
vadduwm %v26, %v24, %v18
vadduwm %v27, %v25, %v18
addi %r8, %r8, 16
or %r9, %r3, %r3
lxvd2x 40, %r9, %r0
vxor %v0, %v0, %v8
vxor %v1, %v1, %v8
vxor %v2, %v2, %v8
vxor %v3, %v3, %v8
vxor %v4, %v4, %v8
vxor %v5, %v5, %v8
vxor %v6, %v6, %v8
vxor %v7, %v7, %v8
vxor %v20, %v20, %v8
vxor %v21, %v21, %v8
vxor %v22, %v22, %v8
vxor %v23, %v23, %v8
vxor %v24, %v24, %v8
vxor %v25, %v25, %v8
vxor %v26, %v26, %v8
vxor %v27, %v27, %v8
addi %r9, %r9, 16
addi %r10, %r4, -1
li %r21, 128
li %r22, 144
lxvd2x 40, %r9, %r0
lxvd2x 46, %r15, %r0
vperm %v14, %v14, %v14, %v29
vcipher %v0, %v0, %v8
vxor %v14, %v14, %v10
addi %r15, %r15, 16
vcipher %v1, %v1, %v8
lxvd2x 48, %r15, %r0
vperm %v16, %v16, %v16, %v29
vcipher %v2, %v2, %v8
addi %r15, %r15, 16
lxvd2x 51, %r16, %r21
vcipher %v3, %v3, %v8
lxvd2x 60, %r16, %r22
addi %r21, %r21, 32
vcipher %v4, %v4, %v8
addi %r22, %r22, 32
vsldoi %v16, %v16, %v16, 8
vcipher %v5, %v5, %v8
vsldoi %v18, %v14, %v16, 8
vsldoi %v17, %v16, %v14, 8
vcipher %v6, %v6, %v8
vsldoi %v17, %v17, %v17, 8
vpmsumd %v16, %v17, %v28
vcipher %v7, %v7, %v8
vpmsumd %v14, %v18, %v19
vpmsumd %v15, %v17, %v19
vcipher %v20, %v20, %v8
vpmsumd %v17, %v18, %v28
vxor %v15, %v15, %v17
vcipher %v21, %v21, %v8
vor %v10, %v14, %v14
vor %v11, %v15, %v15
vcipher %v22, %v22, %v8
vor %v12, %v16, %v16
vcipher %v23, %v23, %v8
vcipher %v24, %v24, %v8
vcipher %v25, %v25, %v8
vcipher %v26, %v26, %v8
vcipher %v27, %v27, %v8
addi %r9, %r9, 16
addi %r10, %r10, -1
li %r12, 2
27:
lxvd2x 40, %r9, %r0
lxvd2x 46, %r15, %r0
vperm %v14, %v14, %v14, %v29
vcipher %v0, %v0, %v8
addi %r15, %r15, 16
lxvd2x 48, %r15, %r0
vcipher %v1, %v1, %v8
vperm %v16, %v16, %v16, %v29
addi %r15, %r15, 16
vcipher %v2, %v2, %v8
lxvd2x 51, %r16, %r21
lxvd2x 60, %r16, %r22
vcipher %v3, %v3, %v8
addi %r21, %r21, 32
addi %r22, %r22, 32
vcipher %v4, %v4, %v8
vsldoi %v16, %v16, %v16, 8
vsldoi %v18, %v14, %v16, 8
vcipher %v5, %v5, %v8
vsldoi %v17, %v16, %v14, 8
vsldoi %v17, %v17, %v17, 8
vcipher %v6, %v6, %v8
vpmsumd %v16, %v17, %v28
vpmsumd %v14, %v18, %v19
vcipher %v7, %v7, %v8
vpmsumd %v15, %v17, %v19
vpmsumd %v17, %v18, %v28
vcipher %v20, %v20, %v8
vxor %v15, %v15, %v17
vxor %v10, %v10, %v14
vcipher %v21, %v21, %v8
vxor %v11, %v11, %v15
vxor %v12, %v12, %v16
vcipher %v22, %v22, %v8
vcipher %v23, %v23, %v8
vcipher %v24, %v24, %v8
vcipher %v25, %v25, %v8
vcipher %v26, %v26, %v8
vcipher %v27, %v27, %v8
addi %r9, %r9, 16
addi %r10, %r10, -1
addi %r12, %r12, -1
cmpldi %cr0, %r12, 0
bne %cr0, 27b
lxvd2x 40, %r9, %r0
lxvd2x 46, %r15, %r0
vperm %v14, %v14, %v14, %v29
vcipher %v0, %v0, %v8
addi %r15, %r15, 16
lxvd2x 48, %r15, %r0
vcipher %v1, %v1, %v8
vperm %v16, %v16, %v16, %v29
addi %r15, %r15, 16
vcipher %v2, %v2, %v8
lxvd2x 51, %r16, %r21
lxvd2x 60, %r16, %r22
vcipher %v3, %v3, %v8
addi %r21, %r21, 32
addi %r22, %r22, 32
vcipher %v4, %v4, %v8
vsldoi %v16, %v16, %v16, 8
vsldoi %v18, %v14, %v16, 8
vcipher %v5, %v5, %v8
vsldoi %v17, %v16, %v14, 8
vsldoi %v17, %v17, %v17, 8
vcipher %v6, %v6, %v8
vpmsumd %v16, %v17, %v28
vpmsumd %v14, %v18, %v19
vcipher %v7, %v7, %v8
vpmsumd %v15, %v17, %v19
vpmsumd %v17, %v18, %v28
vcipher %v20, %v20, %v8
vxor %v15, %v15, %v17
vxor %v14, %v14, %v10
vcipher %v21, %v21, %v8
vxor %v15, %v15, %v11
vxor %v16, %v16, %v12
vcipher %v22, %v22, %v8
vsldoi %v18, %v14, %v30, 8
vpmsumd %v18, %v18, %v13
vcipher %v23, %v23, %v8
vsldoi %v14, %v14, %v14, 8
vxor %v15, %v15, %v14
vcipher %v24, %v24, %v8
vxor %v15, %v15, %v18
vsldoi %v18, %v15, %v30, 8
vcipher %v25, %v25, %v8
vpmsumd %v18, %v18, %v13
vsldoi %v16, %v16, %v16, 8
vcipher %v26, %v26, %v8
vxor %v16, %v16, %v15
vsldoi %v18, %v18, %v18, 8
vcipher %v27, %v27, %v8
vxor %v10, %v16, %v18
vsldoi %v10, %v10, %v10, 8
addi %r9, %r9, 16
addi %r10, %r10, -1
li %r21, 128
li %r22, 144
lxvd2x 40, %r9, %r0
lxvd2x 46, %r15, %r0
vperm %v14, %v14, %v14, %v29
vcipher %v0, %v0, %v8
vxor %v14, %v14, %v10
addi %r15, %r15, 16
vcipher %v1, %v1, %v8
lxvd2x 48, %r15, %r0
vperm %v16, %v16, %v16, %v29
vcipher %v2, %v2, %v8
addi %r15, %r15, 16
lxvd2x 51, %r16, %r21
vcipher %v3, %v3, %v8
lxvd2x 60, %r16, %r22
addi %r21, %r21, 32
vcipher %v4, %v4, %v8
addi %r22, %r22, 32
vsldoi %v16, %v16, %v16, 8
vcipher %v5, %v5, %v8
vsldoi %v18, %v14, %v16, 8
vsldoi %v17, %v16, %v14, 8
vcipher %v6, %v6, %v8
vsldoi %v17, %v17, %v17, 8
vpmsumd %v16, %v17, %v28
vcipher %v7, %v7, %v8
vpmsumd %v14, %v18, %v19
vpmsumd %v15, %v17, %v19
vcipher %v20, %v20, %v8
vpmsumd %v17, %v18, %v28
vxor %v15, %v15, %v17
vcipher %v21, %v21, %v8
vor %v10, %v14, %v14
vor %v11, %v15, %v15
vcipher %v22, %v22, %v8
vor %v12, %v16, %v16
vcipher %v23, %v23, %v8
vcipher %v24, %v24, %v8
vcipher %v25, %v25, %v8
vcipher %v26, %v26, %v8
vcipher %v27, %v27, %v8
addi %r9, %r9, 16
addi %r10, %r10, -1
li %r12, 2
28:
lxvd2x 40, %r9, %r0
lxvd2x 46, %r15, %r0
vperm %v14, %v14, %v14, %v29
vcipher %v0, %v0, %v8
addi %r15, %r15, 16
lxvd2x 48, %r15, %r0
vcipher %v1, %v1, %v8
vperm %v16, %v16, %v16, %v29
addi %r15, %r15, 16
vcipher %v2, %v2, %v8
lxvd2x 51, %r16, %r21
lxvd2x 60, %r16, %r22
vcipher %v3, %v3, %v8
addi %r21, %r21, 32
addi %r22, %r22, 32
vcipher %v4, %v4, %v8
vsldoi %v16, %v16, %v16, 8
vsldoi %v18, %v14, %v16, 8
vcipher %v5, %v5, %v8
vsldoi %v17, %v16, %v14, 8
vsldoi %v17, %v17, %v17, 8
vcipher %v6, %v6, %v8
vpmsumd %v16, %v17, %v28
vpmsumd %v14, %v18, %v19
vcipher %v7, %v7, %v8
vpmsumd %v15, %v17, %v19
vpmsumd %v17, %v18, %v28
vcipher %v20, %v20, %v8
vxor %v15, %v15, %v17
vxor %v10, %v10, %v14
vcipher %v21, %v21, %v8
vxor %v11, %v11, %v15
vxor %v12, %v12, %v16
vcipher %v22, %v22, %v8
vcipher %v23, %v23, %v8
vcipher %v24, %v24, %v8
vcipher %v25, %v25, %v8
vcipher %v26, %v26, %v8
vcipher %v27, %v27, %v8
addi %r9, %r9, 16
addi %r10, %r10, -1
addi %r12, %r12, -1
cmpldi %cr0, %r12, 0
bne %cr0, 28b
lxvd2x 40, %r9, %r0
lxvd2x 46, %r15, %r0
vperm %v14, %v14, %v14, %v29
vcipher %v0, %v0, %v8
addi %r15, %r15, 16
lxvd2x 48, %r15, %r0
vcipher %v1, %v1, %v8
vperm %v16, %v16, %v16, %v29
addi %r15, %r15, 16
vcipher %v2, %v2, %v8
lxvd2x 51, %r16, %r21
lxvd2x 60, %r16, %r22
vcipher %v3, %v3, %v8
addi %r21, %r21, 32
addi %r22, %r22, 32
vcipher %v4, %v4, %v8
vsldoi %v16, %v16, %v16, 8
vsldoi %v18, %v14, %v16, 8
vcipher %v5, %v5, %v8
vsldoi %v17, %v16, %v14, 8
vsldoi %v17, %v17, %v17, 8
vcipher %v6, %v6, %v8
vpmsumd %v16, %v17, %v28
vpmsumd %v14, %v18, %v19
vcipher %v7, %v7, %v8
vpmsumd %v15, %v17, %v19
vpmsumd %v17, %v18, %v28
vcipher %v20, %v20, %v8
vxor %v15, %v15, %v17
vxor %v14, %v14, %v10
vcipher %v21, %v21, %v8
vxor %v15, %v15, %v11
vxor %v16, %v16, %v12
vcipher %v22, %v22, %v8
vsldoi %v18, %v14, %v30, 8
vpmsumd %v18, %v18, %v13
vcipher %v23, %v23, %v8
vsldoi %v14, %v14, %v14, 8
vxor %v15, %v15, %v14
vcipher %v24, %v24, %v8
vxor %v15, %v15, %v18
vsldoi %v18, %v15, %v30, 8
vcipher %v25, %v25, %v8
vpmsumd %v18, %v18, %v13
vsldoi %v16, %v16, %v16, 8
vcipher %v26, %v26, %v8
vxor %v16, %v16, %v15
vsldoi %v18, %v18, %v18, 8
vcipher %v27, %v27, %v8
vxor %v10, %v16, %v18
vsldoi %v10, %v10, %v10, 8
addi %r9, %r9, 16
addi %r10, %r10, -1
29:
lxvd2x 40, %r9, %r0
vcipher %v0, %v0, %v8
vcipher %v1, %v1, %v8
vcipher %v2, %v2, %v8
vcipher %v3, %v3, %v8
vcipher %v4, %v4, %v8
vcipher %v5, %v5, %v8
vcipher %v6, %v6, %v8
vcipher %v7, %v7, %v8
vcipher %v20, %v20, %v8
vcipher %v21, %v21, %v8
vcipher %v22, %v22, %v8
vcipher %v23, %v23, %v8
vcipher %v24, %v24, %v8
vcipher %v25, %v25, %v8
vcipher %v26, %v26, %v8
vcipher %v27, %v27, %v8
addi %r9, %r9, 16
addi %r10, %r10, -1
cmpldi %cr0, %r10, 0
bne %cr0, 29b
lxvd2x 40, %r9, %r0
vcipherlast %v0, %v0, %v8
vcipherlast %v1, %v1, %v8
vcipherlast %v2, %v2, %v8
vcipherlast %v3, %v3, %v8
vcipherlast %v4, %v4, %v8
vcipherlast %v5, %v5, %v8
vcipherlast %v6, %v6, %v8
vcipherlast %v7, %v7, %v8
vcipherlast %v20, %v20, %v8
vcipherlast %v21, %v21, %v8
vcipherlast %v22, %v22, %v8
vcipherlast %v23, %v23, %v8
vcipherlast %v24, %v24, %v8
vcipherlast %v25, %v25, %v8
vcipherlast %v26, %v26, %v8
vcipherlast %v27, %v27, %v8
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v0, %v0, %v9
vperm %v0, %v0, %v0, %v29
stxvd2x 32, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v1, %v1, %v9
vperm %v1, %v1, %v1, %v29
stxvd2x 33, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v2, %v2, %v9
vperm %v2, %v2, %v2, %v29
stxvd2x 34, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v3, %v3, %v9
vperm %v3, %v3, %v3, %v29
stxvd2x 35, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v4, %v4, %v9
vperm %v4, %v4, %v4, %v29
stxvd2x 36, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v5, %v5, %v9
vperm %v5, %v5, %v5, %v29
stxvd2x 37, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v6, %v6, %v9
vperm %v6, %v6, %v6, %v29
stxvd2x 38, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v7, %v7, %v9
vperm %v7, %v7, %v7, %v29
stxvd2x 39, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v20, %v20, %v9
vperm %v20, %v20, %v20, %v29
stxvd2x 52, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v21, %v21, %v9
vperm %v21, %v21, %v21, %v29
stxvd2x 53, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v22, %v22, %v9
vperm %v22, %v22, %v22, %v29
stxvd2x 54, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v23, %v23, %v9
vperm %v23, %v23, %v23, %v29
stxvd2x 55, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v24, %v24, %v9
vperm %v24, %v24, %v24, %v29
stxvd2x 56, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v25, %v25, %v9
vperm %v25, %v25, %v25, %v29
stxvd2x 57, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v26, %v26, %v9
vperm %v26, %v26, %v26, %v29
stxvd2x 58, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v29
vxor %v27, %v27, %v9
vperm %v27, %v27, %v27, %v29
stxvd2x 59, %r6, %r0
addi %r6, %r6, 16
addi %r7, %r7, -16
cmpldi %cr0, %r7, 0
bne %cr0, 26b
b 25f
24:
25:
li %r21, 128
li %r22, 144
lxvd2x 46, %r15, %r0
vperm %v14, %v14, %v14, %v29
vxor %v14, %v14, %v10
addi %r15, %r15, 16
lxvd2x 48, %r15, %r0
vperm %v16, %v16, %v16, %v29
addi %r15, %r15, 16
lxvd2x 51, %r16, %r21
lxvd2x 60, %r16, %r22
addi %r21, %r21, 32
addi %r22, %r22, 32
vsldoi %v16, %v16, %v16, 8
vsldoi %v18, %v14, %v16, 8
vsldoi %v17, %v16, %v14, 8
vsldoi %v17, %v17, %v17, 8
vpmsumd %v16, %v17, %v28
vpmsumd %v14, %v18, %v19
vpmsumd %v15, %v17, %v19
vpmsumd %v17, %v18, %v28
vxor %v15, %v15, %v17
vor %v10, %v14, %v14
vor %v11, %v15, %v15
vor %v12, %v16, %v16
li %r12, 2
210:
lxvd2x 46, %r15, %r0
vperm %v14, %v14, %v14, %v29
addi %r15, %r15, 16
lxvd2x 48, %r15, %r0
vperm %v16, %v16, %v16, %v29
addi %r15, %r15, 16
lxvd2x 51, %r16, %r21
lxvd2x 60, %r16, %r22
addi %r21, %r21, 32
addi %r22, %r22, 32
vsldoi %v16, %v16, %v16, 8
vsldoi %v18, %v14, %v16, 8
vsldoi %v17, %v16, %v14, 8
vsldoi %v17, %v17, %v17, 8
vpmsumd %v16, %v17, %v28
vpmsumd %v14, %v18, %v19
vpmsumd %v15, %v17, %v19
vpmsumd %v17, %v18, %v28
vxor %v15, %v15, %v17
vxor %v10, %v10, %v14
vxor %v11, %v11, %v15
vxor %v12, %v12, %v16
addi %r12, %r12, -1
cmpldi %cr0, %r12, 0
bne %cr0, 210b
lxvd2x 46, %r15, %r0
vperm %v14, %v14, %v14, %v29
addi %r15, %r15, 16
lxvd2x 48, %r15, %r0
vperm %v16, %v16, %v16, %v29
addi %r15, %r15, 16
lxvd2x 51, %r16, %r21
lxvd2x 60, %r16, %r22
addi %r21, %r21, 32
addi %r22, %r22, 32
vsldoi %v16, %v16, %v16, 8
vsldoi %v18, %v14, %v16, 8
vsldoi %v17, %v16, %v14, 8
vsldoi %v17, %v17, %v17, 8
vpmsumd %v16, %v17, %v28
vpmsumd %v14, %v18, %v19
vpmsumd %v15, %v17, %v19
vpmsumd %v17, %v18, %v28
vxor %v15, %v15, %v17
vxor %v14, %v14, %v10
vxor %v15, %v15, %v11
vxor %v16, %v16, %v12
vsldoi %v18, %v14, %v30, 8
vpmsumd %v18, %v18, %v13
vsldoi %v14, %v14, %v14, 8
vxor %v15, %v15, %v14
vxor %v15, %v15, %v18
vsldoi %v18, %v15, %v30, 8
vpmsumd %v18, %v18, %v13
vsldoi %v16, %v16, %v16, 8
vxor %v16, %v16, %v15
vsldoi %v18, %v18, %v18, 8
vxor %v10, %v16, %v18
vsldoi %v10, %v10, %v10, 8
li %r21, 128
li %r22, 144
lxvd2x 46, %r15, %r0
vperm %v14, %v14, %v14, %v29
vxor %v14, %v14, %v10
addi %r15, %r15, 16
lxvd2x 48, %r15, %r0
vperm %v16, %v16, %v16, %v29
addi %r15, %r15, 16
lxvd2x 51, %r16, %r21
lxvd2x 60, %r16, %r22
addi %r21, %r21, 32
addi %r22, %r22, 32
vsldoi %v16, %v16, %v16, 8
vsldoi %v18, %v14, %v16, 8
vsldoi %v17, %v16, %v14, 8
vsldoi %v17, %v17, %v17, 8
vpmsumd %v16, %v17, %v28
vpmsumd %v14, %v18, %v19
vpmsumd %v15, %v17, %v19
vpmsumd %v17, %v18, %v28
vxor %v15, %v15, %v17
vor %v10, %v14, %v14
vor %v11, %v15, %v15
vor %v12, %v16, %v16
li %r12, 2
211:
lxvd2x 46, %r15, %r0
vperm %v14, %v14, %v14, %v29
addi %r15, %r15, 16
lxvd2x 48, %r15, %r0
vperm %v16, %v16, %v16, %v29
addi %r15, %r15, 16
lxvd2x 51, %r16, %r21
lxvd2x 60, %r16, %r22
addi %r21, %r21, 32
addi %r22, %r22, 32
vsldoi %v16, %v16, %v16, 8
vsldoi %v18, %v14, %v16, 8
vsldoi %v17, %v16, %v14, 8
vsldoi %v17, %v17, %v17, 8
vpmsumd %v16, %v17, %v28
vpmsumd %v14, %v18, %v19
vpmsumd %v15, %v17, %v19
vpmsumd %v17, %v18, %v28
vxor %v15, %v15, %v17
vxor %v10, %v10, %v14
vxor %v11, %v11, %v15
vxor %v12, %v12, %v16
addi %r12, %r12, -1
cmpldi %cr0, %r12, 0
bne %cr0, 211b
lxvd2x 46, %r15, %r0
vperm %v14, %v14, %v14, %v29
addi %r15, %r15, 16
lxvd2x 48, %r15, %r0
vperm %v16, %v16, %v16, %v29
addi %r15, %r15, 16
lxvd2x 51, %r16, %r21
lxvd2x 60, %r16, %r22
addi %r21, %r21, 32
addi %r22, %r22, 32
vsldoi %v16, %v16, %v16, 8
vsldoi %v18, %v14, %v16, 8
vsldoi %v17, %v16, %v14, 8
vsldoi %v17, %v17, %v17, 8
vpmsumd %v16, %v17, %v28
vpmsumd %v14, %v18, %v19
vpmsumd %v15, %v17, %v19
vpmsumd %v17, %v18, %v28
vxor %v15, %v15, %v17
vxor %v14, %v14, %v10
vxor %v15, %v15, %v11
vxor %v16, %v16, %v12
vsldoi %v18, %v14, %v30, 8
vpmsumd %v18, %v18, %v13
vsldoi %v14, %v14, %v14, 8
vxor %v15, %v15, %v14
vxor %v15, %v15, %v18
vsldoi %v18, %v15, %v30, 8
vpmsumd %v18, %v18, %v13
vsldoi %v16, %v16, %v16, 8
vxor %v16, %v16, %v15
vsldoi %v18, %v18, %v18, 8
vxor %v10, %v16, %v18
vsldoi %v10, %v10, %v10, 8
li %r11, 12
stwbrx %r8, %r5, %r11
lxvd2x 40, %r16, %r25
vperm %v10, %v10, %v10, %v8
stxvd2x 42, %r14, %r0
li %r11, 640
lxvd2x 52, %r16, %r11
li %r11, 656
lxvd2x 53, %r16, %r11
li %r11, 672
lxvd2x 54, %r16, %r11
li %r11, 688
lxvd2x 55, %r16, %r11
li %r11, 704
lxvd2x 56, %r16, %r11
li %r11, 720
lxvd2x 57, %r16, %r11
li %r11, 736
lxvd2x 58, %r16, %r11
li %r11, 752
lxvd2x 59, %r16, %r11
li %r11, 768
lxvd2x 60, %r16, %r11
li %r11, 784
lxvd2x 61, %r16, %r11
li %r11, 800
lxvd2x 62, %r16, %r11
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
.globl gcm_stitched16_abi
.type gcm_stitched16_abi,@function
gcm_stitched16_abi:
std %r31, 1856(%r10)
mflr %r0
std %r0, 1864(%r10)
or %r31, %r10, %r10
li %r11, 1536
stxvd2x 52, %r31, %r11
li %r11, 1024
lxvd2x 52, %r31, %r11
li %r11, 1552
stxvd2x 53, %r31, %r11
li %r11, 1040
lxvd2x 53, %r31, %r11
li %r11, 1568
stxvd2x 54, %r31, %r11
li %r11, 1056
lxvd2x 54, %r31, %r11
li %r11, 1584
stxvd2x 55, %r31, %r11
li %r11, 1072
lxvd2x 55, %r31, %r11
li %r11, 1600
stxvd2x 56, %r31, %r11
li %r11, 1088
lxvd2x 56, %r31, %r11
li %r11, 1616
stxvd2x 57, %r31, %r11
li %r11, 1104
lxvd2x 57, %r31, %r11
li %r11, 1632
stxvd2x 58, %r31, %r11
li %r11, 1120
lxvd2x 58, %r31, %r11
li %r11, 1648
stxvd2x 59, %r31, %r11
li %r11, 1136
lxvd2x 59, %r31, %r11
li %r11, 1664
stxvd2x 60, %r31, %r11
li %r11, 1152
lxvd2x 60, %r31, %r11
li %r11, 1680
stxvd2x 61, %r31, %r11
li %r11, 1168
lxvd2x 61, %r31, %r11
li %r11, 1696
stxvd2x 62, %r31, %r11
li %r11, 1184
lxvd2x 62, %r31, %r11
li %r11, 1712
stxvd2x 63, %r31, %r11
li %r11, 1200
lxvd2x 63, %r31, %r11
bl gcm_stitched16
li %r11, 1280
stxvd2x 52, %r31, %r11
li %r11, 1536
lxvd2x 52, %r31, %r11
li %r11, 1296
stxvd2x 53, %r31, %r11
li %r11, 1552
lxvd2x 53, %r31, %r11
li %r11, 1312
stxvd2x 54, %r31, %r11
li %r11, 1568
lxvd2x 54, %r31, %r11
li %r11, 1328
stxvd2x 55, %r31, %r11
li %r11, 1584
lxvd2x 55, %r31, %r11
li %r11, 1344
stxvd2x 56, %r31, %r11
li %r11, 1600
lxvd2x 56, %r31, %r11
li %r11, 1360
stxvd2x 57, %r31, %r11
li %r11, 1616
lxvd2x 57, %r31, %r11
li %r11, 1376
stxvd2x 58, %r31, %r11
li %r11, 1632
lxvd2x 58, %r31, %r11
li %r11, 1392
stxvd2x 59, %r31, %r11
li %r11, 1648
lxvd2x 59, %r31, %r11
li %r11, 1408
stxvd2x 60, %r31, %r11
li %r11, 1664
lxvd2x 60, %r31, %r11
li %r11, 1424
stxvd2x 61, %r31, %r11
li %r11, 1680
lxvd2x 61, %r31, %r11
li %r11, 1440
stxvd2x 62, %r31, %r11
li %r11, 1696
lxvd2x 62, %r31, %r11
li %r11, 1456
stxvd2x 63, %r31, %r11
li %r11, 1712
lxvd2x 63, %r31, %r11
ld %r0, 1864(%r31)
mtlr %r0
or %r12, %r31, %r31
ld %r31, 1856(%r12)
blr
