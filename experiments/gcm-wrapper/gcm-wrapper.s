.text
.abiversion 2
.globl gcm_encrypt_blocks
.type gcm_encrypt_blocks,@function
gcm_encrypt_blocks:
cmpldi %cr0, %r8, 0
beq %cr0, 20f
std %r25, 0(%r9)
std %r26, 8(%r9)
std %r27, 16(%r9)
std %r28, 24(%r9)
std %r29, 32(%r9)
std %r30, 40(%r9)
std %r31, 48(%r9)
mflr %r0
std %r0, 56(%r9)
or %r29, %r3, %r3
or %r28, %r4, %r4
or %r27, %r5, %r5
or %r26, %r6, %r6
or %r30, %r7, %r7
or %r25, %r8, %r8
or %r31, %r9, %r9
rldicl %r12, %r25, 59, 5
cmpldi %cr0, %r12, 0
beq %cr0, 22f
or %r3, %r29, %r29
or %r4, %r28, %r28
or %r5, %r27, %r27
or %r6, %r30, %r30
li %r0, 7
and %r11, %r25, %r0
subf %r7, %r11, %r25
addi %r8, %r29, 240
or %r9, %r26, %r26
addi %r10, %r31, 64
cmpldi %cr0, %r7, 0
beq %cr0, 24f
std %r14, 0(%r10)
std %r15, 8(%r10)
std %r16, 16(%r10)
std %r20, 40(%r10)
std %r21, 48(%r10)
std %r22, 56(%r10)
std %r23, 64(%r10)
std %r24, 72(%r10)
std %r18, 80(%r10)
or %r16, %r10, %r10
addi %r16, %r16, 128
or %r14, %r9, %r9
li %r15, 112
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
addi %r24, %r16, 256
li %r18, 96
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
lxvd2x 42, %r14, %r0
vperm %v10, %v10, %v10, %v19
li %r11, 12
lwbrx %r8, %r5, %r11
or %r9, %r3, %r3
vor %v12, %v11, %v11
vor %v8, %v12, %v12
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
vsldoi %v9, %v8, %v8, 8
vsldoi %v18, %v9, %v12, 8
vsldoi %v18, %v18, %v18, 8
vsldoi %v8, %v12, %v9, 8
li %r11, 224
stxvd2x 40, %r16, %r11
li %r11, 240
stxvd2x 50, %r16, %r11
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
vor %v8, %v12, %v12
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
vsldoi %v9, %v8, %v8, 8
vsldoi %v18, %v9, %v12, 8
vsldoi %v18, %v18, %v18, 8
vsldoi %v8, %v12, %v9, 8
li %r11, 192
stxvd2x 40, %r16, %r11
li %r11, 208
stxvd2x 50, %r16, %r11
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
vor %v8, %v12, %v12
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
vsldoi %v9, %v8, %v8, 8
vsldoi %v18, %v9, %v12, 8
vsldoi %v18, %v18, %v18, 8
vsldoi %v8, %v12, %v9, 8
li %r11, 160
stxvd2x 40, %r16, %r11
li %r11, 176
stxvd2x 50, %r16, %r11
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
vor %v8, %v12, %v12
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
vsldoi %v9, %v8, %v8, 8
vsldoi %v18, %v9, %v12, 8
vsldoi %v18, %v18, %v18, 8
vsldoi %v8, %v12, %v9, 8
li %r11, 128
stxvd2x 40, %r16, %r11
li %r11, 144
stxvd2x 50, %r16, %r11
or %r11, %r24, %r24
addi %r12, %r4, 1
26:
lxvd2x 40, %r9, %r0
vperm %v8, %v8, %v8, %v19
stxvd2x 40, %r11, %r0
addi %r9, %r9, 16
addi %r11, %r11, 16
addi %r12, %r12, -1
cmpldi %cr0, %r12, 0
bne %cr0, 26b
or %r3, %r24, %r24
li %r23, 64
li %r24, 80
lxvd2x 32, %r5, %r0
vperm %v0, %v0, %v0, %v19
stxvd2x 32, %r16, %r15
27:
lxvd2x 32, %r16, %r15
lxvd2x 49, %r16, %r20
vadduwm %v18, %v17, %v17
vadduwm %v1, %v0, %v17
vadduwm %v2, %v0, %v18
vadduwm %v3, %v1, %v18
vadduwm %v4, %v2, %v18
vadduwm %v5, %v3, %v18
vadduwm %v6, %v4, %v18
vadduwm %v7, %v5, %v18
vadduwm %v18, %v6, %v18
stxvd2x 50, %r16, %r15
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
li %r21, 32
lxvd2x 41, %r3, %r21
li %r22, 48
lxvd2x 43, %r3, %r22
lxvd2x 44, %r3, %r23
lxvd2x 46, %r3, %r24
lxvd2x 47, %r3, %r18
li %r11, 112
lxvd2x 48, %r3, %r11
li %r12, 128
lxvd2x 49, %r3, %r12
addi %r9, %r3, 144
lxvd2x 50, %r9, %r0
vcipher %v0, %v0, %v8
vcipher %v1, %v1, %v8
vcipher %v2, %v2, %v8
vcipher %v3, %v3, %v8
vcipher %v4, %v4, %v8
vcipher %v5, %v5, %v8
vcipher %v6, %v6, %v8
vcipher %v7, %v7, %v8
vcipher %v0, %v0, %v9
vcipher %v1, %v1, %v9
vcipher %v2, %v2, %v9
vcipher %v3, %v3, %v9
vcipher %v4, %v4, %v9
vcipher %v5, %v5, %v9
vcipher %v6, %v6, %v9
vcipher %v7, %v7, %v9
vcipher %v0, %v0, %v11
vcipher %v1, %v1, %v11
vcipher %v2, %v2, %v11
vcipher %v3, %v3, %v11
vcipher %v4, %v4, %v11
vcipher %v5, %v5, %v11
vcipher %v6, %v6, %v11
vcipher %v7, %v7, %v11
vcipher %v0, %v0, %v12
vcipher %v1, %v1, %v12
vcipher %v2, %v2, %v12
vcipher %v3, %v3, %v12
vcipher %v4, %v4, %v12
vcipher %v5, %v5, %v12
vcipher %v6, %v6, %v12
vcipher %v7, %v7, %v12
vcipher %v0, %v0, %v14
vcipher %v1, %v1, %v14
vcipher %v2, %v2, %v14
vcipher %v3, %v3, %v14
vcipher %v4, %v4, %v14
vcipher %v5, %v5, %v14
vcipher %v6, %v6, %v14
vcipher %v7, %v7, %v14
vcipher %v0, %v0, %v15
vcipher %v1, %v1, %v15
vcipher %v2, %v2, %v15
vcipher %v3, %v3, %v15
vcipher %v4, %v4, %v15
vcipher %v5, %v5, %v15
vcipher %v6, %v6, %v15
vcipher %v7, %v7, %v15
vcipher %v0, %v0, %v16
vcipher %v1, %v1, %v16
vcipher %v2, %v2, %v16
vcipher %v3, %v3, %v16
vcipher %v4, %v4, %v16
vcipher %v5, %v5, %v16
vcipher %v6, %v6, %v16
vcipher %v7, %v7, %v16
vcipher %v0, %v0, %v17
vcipher %v1, %v1, %v17
vcipher %v2, %v2, %v17
vcipher %v3, %v3, %v17
vcipher %v4, %v4, %v17
vcipher %v5, %v5, %v17
vcipher %v6, %v6, %v17
vcipher %v7, %v7, %v17
vcipher %v0, %v0, %v18
vcipher %v1, %v1, %v18
vcipher %v2, %v2, %v18
vcipher %v3, %v3, %v18
vcipher %v4, %v4, %v18
vcipher %v5, %v5, %v18
vcipher %v6, %v6, %v18
vcipher %v7, %v7, %v18
addi %r9, %r3, 160
addi %r10, %r4, -10
cmpldi %cr0, %r10, 0
beq %cr0, 28f
210:
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
bne %cr0, 210b
b 29f
28:
29:
lxvd2x 40, %r9, %r0
vcipherlast %v0, %v0, %v8
vcipherlast %v1, %v1, %v8
vcipherlast %v2, %v2, %v8
vcipherlast %v3, %v3, %v8
vcipherlast %v4, %v4, %v8
vcipherlast %v5, %v5, %v8
vcipherlast %v6, %v6, %v8
vcipherlast %v7, %v7, %v8
lxvd2x 40, %r6, %r0
lxvd2x 41, %r6, %r20
lxvd2x 43, %r6, %r21
lxvd2x 44, %r6, %r22
lxvd2x 46, %r6, %r23
lxvd2x 47, %r6, %r24
lxvd2x 48, %r6, %r18
lxvd2x 49, %r6, %r11
vperm %v8, %v8, %v8, %v19
vxor %v0, %v0, %v8
vperm %v9, %v9, %v9, %v19
vxor %v1, %v1, %v9
vperm %v11, %v11, %v11, %v19
vxor %v2, %v2, %v11
vperm %v12, %v12, %v12, %v19
vxor %v3, %v3, %v12
vperm %v14, %v14, %v14, %v19
vxor %v4, %v4, %v14
vperm %v15, %v15, %v15, %v19
vxor %v5, %v5, %v15
vperm %v16, %v16, %v16, %v19
vxor %v6, %v6, %v16
vperm %v17, %v17, %v17, %v19
vxor %v7, %v7, %v17
vperm %v8, %v0, %v0, %v19
stxvd2x 40, %r6, %r0
vperm %v9, %v1, %v1, %v19
stxvd2x 41, %r6, %r20
vperm %v11, %v2, %v2, %v19
stxvd2x 43, %r6, %r21
vperm %v12, %v3, %v3, %v19
stxvd2x 44, %r6, %r22
vperm %v14, %v4, %v4, %v19
stxvd2x 46, %r6, %r23
vperm %v15, %v5, %v5, %v19
stxvd2x 47, %r6, %r24
vperm %v16, %v6, %v6, %v19
stxvd2x 48, %r6, %r18
vperm %v17, %v7, %v7, %v19
stxvd2x 49, %r6, %r11
addi %r6, %r6, 128
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
bne %cr0, 27b
li %r11, 12
stwbrx %r8, %r5, %r11
vperm %v10, %v10, %v10, %v19
stxvd2x 42, %r14, %r0
addi %r12, %r16, -128
ld %r14, 0(%r12)
ld %r15, 8(%r12)
ld %r16, 16(%r12)
ld %r20, 40(%r12)
ld %r21, 48(%r12)
ld %r22, 56(%r12)
ld %r23, 64(%r12)
ld %r24, 72(%r12)
ld %r18, 80(%r12)
b 25f
24:
25:
li %r0, 7
and %r11, %r25, %r0
subf %r12, %r11, %r25
rldicr %r12, %r12, 4, 59
add %r30, %r30, %r12
or %r25, %r11, %r11
b 23f
22:
23:
cmpldi %cr0, %r25, 0
beq %cr0, 211f
or %r3, %r29, %r29
or %r4, %r28, %r28
or %r5, %r27, %r27
or %r6, %r30, %r30
or %r7, %r25, %r25
addi %r8, %r31, 64
bl vg_aes_ctr32
addi %r3, %r29, 240
or %r4, %r26, %r26
or %r5, %r30, %r30
or %r6, %r25, %r25
addi %r7, %r31, 64
bl vg_ghash
b 212f
211:
212:
ld %r0, 56(%r31)
mtlr %r0
or %r12, %r31, %r31
ld %r25, 0(%r12)
ld %r26, 8(%r12)
ld %r27, 16(%r12)
ld %r28, 24(%r12)
ld %r29, 32(%r12)
ld %r30, 40(%r12)
ld %r31, 48(%r12)
b 21f
20:
21:
blr
.globl vg_aes_ctr32
.type vg_aes_ctr32,@function
vg_aes_ctr32:
cmpldi %cr0, %r7, 0
beq %cr0, 20f
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
lis %r11, 1
ori %r11, %r11, 515
rldicr %r11, %r11, 32, 31
oris %r11, %r11, 1029
ori %r11, %r11, 1543
lis %r12, 2057
ori %r12, %r12, 2571
rldicr %r12, %r12, 32, 31
oris %r12, %r12, 5141
ori %r12, %r12, 5655
mtvsrd 50, %r11
mtvsrd 33, %r12
vsldoi %v18, %v0, %v18, 8
vsldoi %v18, %v18, %v1, 8
li %r11, 12
lwbrx %r8, %r5, %r11
lxvd2x 42, %r5, %r0
vperm %v10, %v10, %v10, %v19
rldicl %r12, %r7, 61, 3
cmpldi %cr0, %r12, 0
beq %cr0, 22f
24:
mtvsrd 43, %r8
vperm %v0, %v10, %v11, %v18
addi %r8, %r8, 1
mtvsrd 43, %r8
vperm %v1, %v10, %v11, %v18
addi %r8, %r8, 1
mtvsrd 43, %r8
vperm %v2, %v10, %v11, %v18
addi %r8, %r8, 1
mtvsrd 43, %r8
vperm %v3, %v10, %v11, %v18
addi %r8, %r8, 1
mtvsrd 43, %r8
vperm %v4, %v10, %v11, %v18
addi %r8, %r8, 1
mtvsrd 43, %r8
vperm %v5, %v10, %v11, %v18
addi %r8, %r8, 1
mtvsrd 43, %r8
vperm %v6, %v10, %v11, %v18
addi %r8, %r8, 1
mtvsrd 43, %r8
vperm %v7, %v10, %v11, %v18
addi %r8, %r8, 1
or %r9, %r3, %r3
lxvd2x 40, %r9, %r0
vperm %v8, %v8, %v8, %v19
vxor %v0, %v0, %v8
vxor %v1, %v1, %v8
vxor %v2, %v2, %v8
vxor %v3, %v3, %v8
vxor %v4, %v4, %v8
vxor %v5, %v5, %v8
vxor %v6, %v6, %v8
vxor %v7, %v7, %v8
addi %r9, %r9, 16
addi %r10, %r4, -1
25:
lxvd2x 40, %r9, %r0
vperm %v8, %v8, %v8, %v19
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
bne %cr0, 25b
lxvd2x 40, %r9, %r0
vperm %v8, %v8, %v8, %v19
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
vperm %v0, %v0, %v0, %v19
stxvd2x 32, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v1, %v1, %v9
vperm %v1, %v1, %v1, %v19
stxvd2x 33, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v2, %v2, %v9
vperm %v2, %v2, %v2, %v19
stxvd2x 34, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v3, %v3, %v9
vperm %v3, %v3, %v3, %v19
stxvd2x 35, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v4, %v4, %v9
vperm %v4, %v4, %v4, %v19
stxvd2x 36, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v5, %v5, %v9
vperm %v5, %v5, %v5, %v19
stxvd2x 37, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v6, %v6, %v9
vperm %v6, %v6, %v6, %v19
stxvd2x 38, %r6, %r0
addi %r6, %r6, 16
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v7, %v7, %v9
vperm %v7, %v7, %v7, %v19
stxvd2x 39, %r6, %r0
addi %r6, %r6, 16
addi %r7, %r7, -8
rldicl %r12, %r7, 61, 3
cmpldi %cr0, %r12, 0
bne %cr0, 24b
b 23f
22:
23:
cmpldi %cr0, %r7, 0
beq %cr0, 26f
28:
mtvsrd 43, %r8
vperm %v0, %v10, %v11, %v18
addi %r8, %r8, 1
or %r9, %r3, %r3
lxvd2x 40, %r9, %r0
vperm %v8, %v8, %v8, %v19
vxor %v0, %v0, %v8
addi %r9, %r9, 16
addi %r10, %r4, -1
29:
lxvd2x 40, %r9, %r0
vperm %v8, %v8, %v8, %v19
vcipher %v0, %v0, %v8
addi %r9, %r9, 16
addi %r10, %r10, -1
cmpldi %cr0, %r10, 0
bne %cr0, 29b
lxvd2x 40, %r9, %r0
vperm %v8, %v8, %v8, %v19
vcipherlast %v0, %v0, %v8
lxvd2x 41, %r6, %r0
vperm %v9, %v9, %v9, %v19
vxor %v0, %v0, %v9
vperm %v0, %v0, %v0, %v19
stxvd2x 32, %r6, %r0
addi %r6, %r6, 16
addi %r7, %r7, -1
cmpldi %cr0, %r7, 0
bne %cr0, 28b
b 27f
26:
27:
stwbrx %r8, %r5, %r11
b 21f
20:
21:
blr
.globl vg_ghash
.type vg_ghash,@function
vg_ghash:
cmpldi %cr0, %r6, 0
beq %cr0, 20f
li %r0, 0
vxor %v19, %v19, %v19
lis %r8, -15872
ori %r8, %r8, 0
rldicr %r8, %r8, 32, 31
oris %r8, %r8, 0
ori %r8, %r8, 0
mtvsrd 33, %r8
mtvsrd 39, %r8
vsldoi %v1, %v19, %v1, 8
vsldoi %v1, %v1, %v7, 8
lis %r8, 3854
ori %r8, %r8, 3340
rldicr %r8, %r8, 32, 31
oris %r8, %r8, 2826
ori %r8, %r8, 2312
lis %r9, 1798
ori %r9, %r9, 1284
rldicr %r9, %r9, 32, 31
oris %r9, %r9, 770
ori %r9, %r9, 256
mtvsrd 50, %r8
mtvsrd 39, %r9
vsldoi %v18, %v19, %v18, 8
vsldoi %v18, %v18, %v7, 8
lis %r8, 17920
ori %r8, %r8, 0
rldicr %r8, %r8, 32, 31
oris %r8, %r8, 0
ori %r8, %r8, 0
li %r9, 3
mtvsrd 48, %r8
mtvsrd 39, %r9
vsldoi %v16, %v19, %v16, 8
vsldoi %v16, %v16, %v7, 8
lxvd2x 38, %r3, %r0
vperm %v6, %v6, %v6, %v18
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v16
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v16
vpmsumd %v4, %v6, %v16
vsldoi %v7, %v3, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v3, %v3, %v3, 8
vxor %v4, %v4, %v3
vxor %v4, %v4, %v7
vsldoi %v7, %v4, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v5, %v5, %v5, 8
vxor %v5, %v5, %v4
vsldoi %v7, %v7, %v7, 8
vxor %v16, %v5, %v7
vsldoi %v16, %v16, %v16, 8
lxvd2x 32, %r4, %r0
vperm %v0, %v0, %v0, %v18
rldicl %r10, %r6, 60, 4
cmpldi %cr0, %r10, 0
beq %cr0, 22f
vsldoi %v6, %v16, %v16, 8
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v16
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v16
vpmsumd %v4, %v6, %v16
vsldoi %v7, %v3, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v3, %v3, %v3, 8
vxor %v4, %v4, %v3
vxor %v4, %v4, %v7
vsldoi %v7, %v4, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v5, %v5, %v5, 8
vxor %v5, %v5, %v4
vsldoi %v7, %v7, %v7, 8
vxor %v8, %v5, %v7
vsldoi %v8, %v8, %v8, 8
vsldoi %v6, %v8, %v8, 8
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v16
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v16
vpmsumd %v4, %v6, %v16
vsldoi %v7, %v3, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v3, %v3, %v3, 8
vxor %v4, %v4, %v3
vxor %v4, %v4, %v7
vsldoi %v7, %v4, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v5, %v5, %v5, 8
vxor %v5, %v5, %v4
vsldoi %v7, %v7, %v7, 8
vxor %v9, %v5, %v7
vsldoi %v9, %v9, %v9, 8
vsldoi %v6, %v9, %v9, 8
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v16
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v16
vpmsumd %v4, %v6, %v16
vsldoi %v7, %v3, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v3, %v3, %v3, 8
vxor %v4, %v4, %v3
vxor %v4, %v4, %v7
vsldoi %v7, %v4, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v5, %v5, %v5, 8
vxor %v5, %v5, %v4
vsldoi %v7, %v7, %v7, 8
vxor %v10, %v5, %v7
vsldoi %v10, %v10, %v10, 8
vsldoi %v6, %v10, %v10, 8
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v16
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v16
vpmsumd %v4, %v6, %v16
vsldoi %v7, %v3, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v3, %v3, %v3, 8
vxor %v4, %v4, %v3
vxor %v4, %v4, %v7
vsldoi %v7, %v4, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v5, %v5, %v5, 8
vxor %v5, %v5, %v4
vsldoi %v7, %v7, %v7, 8
vxor %v11, %v5, %v7
vsldoi %v11, %v11, %v11, 8
vsldoi %v6, %v11, %v11, 8
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v16
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v16
vpmsumd %v4, %v6, %v16
vsldoi %v7, %v3, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v3, %v3, %v3, 8
vxor %v4, %v4, %v3
vxor %v4, %v4, %v7
vsldoi %v7, %v4, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v5, %v5, %v5, 8
vxor %v5, %v5, %v4
vsldoi %v7, %v7, %v7, 8
vxor %v12, %v5, %v7
vsldoi %v12, %v12, %v12, 8
vsldoi %v6, %v12, %v12, 8
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v16
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v16
vpmsumd %v4, %v6, %v16
vsldoi %v7, %v3, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v3, %v3, %v3, 8
vxor %v4, %v4, %v3
vxor %v4, %v4, %v7
vsldoi %v7, %v4, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v5, %v5, %v5, 8
vxor %v5, %v5, %v4
vsldoi %v7, %v7, %v7, 8
vxor %v13, %v5, %v7
vsldoi %v13, %v13, %v13, 8
vsldoi %v6, %v13, %v13, 8
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v16
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v16
vpmsumd %v4, %v6, %v16
vsldoi %v7, %v3, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v3, %v3, %v3, 8
vxor %v4, %v4, %v3
vxor %v4, %v4, %v7
vsldoi %v7, %v4, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v5, %v5, %v5, 8
vxor %v5, %v5, %v4
vsldoi %v7, %v7, %v7, 8
vxor %v14, %v5, %v7
vsldoi %v14, %v14, %v14, 8
vsldoi %v6, %v13, %v13, 8
vsldoi %v7, %v6, %v14, 8
vsldoi %v7, %v7, %v7, 8
vsldoi %v14, %v14, %v6, 8
vor %v13, %v7, %v7
vsldoi %v6, %v11, %v11, 8
vsldoi %v7, %v6, %v12, 8
vsldoi %v7, %v7, %v7, 8
vsldoi %v12, %v12, %v6, 8
vor %v11, %v7, %v7
vsldoi %v6, %v9, %v9, 8
vsldoi %v7, %v6, %v10, 8
vsldoi %v7, %v7, %v7, 8
vsldoi %v10, %v10, %v6, 8
vor %v9, %v7, %v7
vsldoi %v6, %v16, %v16, 8
vsldoi %v7, %v6, %v8, 8
vsldoi %v7, %v7, %v7, 8
vsldoi %v8, %v8, %v6, 8
vor %v15, %v7, %v7
24:
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
addi %r5, %r5, 16
vxor %v6, %v6, %v0
lxvd2x 37, %r5, %r0
vperm %v5, %v5, %v5, %v18
addi %r5, %r5, 16
vsldoi %v5, %v5, %v5, 8
vsldoi %v2, %v6, %v5, 8
vsldoi %v7, %v5, %v6, 8
vsldoi %v7, %v7, %v7, 8
vpmsumd %v5, %v2, %v13
vpmsumd %v3, %v7, %v14
vpmsumd %v4, %v2, %v14
vpmsumd %v2, %v7, %v13
vxor %v4, %v4, %v2
vor %v0, %v3, %v3
vor %v16, %v4, %v4
vor %v17, %v5, %v5
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
addi %r5, %r5, 16
lxvd2x 37, %r5, %r0
vperm %v5, %v5, %v5, %v18
addi %r5, %r5, 16
vsldoi %v5, %v5, %v5, 8
vsldoi %v2, %v6, %v5, 8
vsldoi %v7, %v5, %v6, 8
vsldoi %v7, %v7, %v7, 8
vpmsumd %v5, %v2, %v11
vpmsumd %v3, %v7, %v12
vpmsumd %v4, %v2, %v12
vpmsumd %v2, %v7, %v11
vxor %v4, %v4, %v2
vxor %v0, %v0, %v3
vxor %v16, %v16, %v4
vxor %v17, %v17, %v5
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
addi %r5, %r5, 16
lxvd2x 37, %r5, %r0
vperm %v5, %v5, %v5, %v18
addi %r5, %r5, 16
vsldoi %v5, %v5, %v5, 8
vsldoi %v2, %v6, %v5, 8
vsldoi %v7, %v5, %v6, 8
vsldoi %v7, %v7, %v7, 8
vpmsumd %v5, %v2, %v9
vpmsumd %v3, %v7, %v10
vpmsumd %v4, %v2, %v10
vpmsumd %v2, %v7, %v9
vxor %v4, %v4, %v2
vxor %v0, %v0, %v3
vxor %v16, %v16, %v4
vxor %v17, %v17, %v5
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
addi %r5, %r5, 16
lxvd2x 37, %r5, %r0
vperm %v5, %v5, %v5, %v18
addi %r5, %r5, 16
vsldoi %v5, %v5, %v5, 8
vsldoi %v2, %v6, %v5, 8
vsldoi %v7, %v5, %v6, 8
vsldoi %v7, %v7, %v7, 8
vpmsumd %v5, %v2, %v15
vpmsumd %v3, %v7, %v8
vpmsumd %v4, %v2, %v8
vpmsumd %v2, %v7, %v15
vxor %v4, %v4, %v2
vxor %v3, %v3, %v0
vxor %v4, %v4, %v16
vxor %v5, %v5, %v17
vsldoi %v7, %v3, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v3, %v3, %v3, 8
vxor %v4, %v4, %v3
vxor %v4, %v4, %v7
vsldoi %v7, %v4, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v5, %v5, %v5, 8
vxor %v5, %v5, %v4
vsldoi %v7, %v7, %v7, 8
vxor %v0, %v5, %v7
addi %r6, %r6, -8
rldicl %r10, %r6, 61, 3
cmpldi %cr0, %r10, 0
bne %cr0, 24b
vsldoi %v6, %v8, %v8, 8
vsldoi %v16, %v15, %v6, 8
cmpldi %cr0, %r6, 0
beq %cr0, 25f
27:
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
vxor %v6, %v6, %v0
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v16
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v16
vpmsumd %v4, %v6, %v16
vsldoi %v7, %v3, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v3, %v3, %v3, 8
vxor %v4, %v4, %v3
vxor %v4, %v4, %v7
vsldoi %v7, %v4, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v5, %v5, %v5, 8
vxor %v5, %v5, %v4
vsldoi %v7, %v7, %v7, 8
vxor %v0, %v5, %v7
addi %r5, %r5, 16
addi %r6, %r6, -1
cmpldi %cr0, %r6, 0
bne %cr0, 27b
b 26f
25:
26:
vperm %v7, %v0, %v0, %v18
stxvd2x 39, %r4, %r0
b 23f
22:
28:
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
vxor %v6, %v6, %v0
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v16
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v16
vpmsumd %v4, %v6, %v16
vsldoi %v7, %v3, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v3, %v3, %v3, 8
vxor %v4, %v4, %v3
vxor %v4, %v4, %v7
vsldoi %v7, %v4, %v19, 8
vpmsumd %v7, %v7, %v1
vsldoi %v5, %v5, %v5, 8
vxor %v5, %v5, %v4
vsldoi %v7, %v7, %v7, 8
vxor %v0, %v5, %v7
addi %r5, %r5, 16
addi %r6, %r6, -1
cmpldi %cr0, %r6, 0
bne %cr0, 28b
vperm %v7, %v0, %v0, %v18
stxvd2x 39, %r4, %r0
23:
b 21f
20:
21:
blr
