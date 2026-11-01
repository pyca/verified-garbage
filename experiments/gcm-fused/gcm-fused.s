.text
.abiversion 2
.globl gcm_fused
.type gcm_fused,@function
gcm_fused:
cmpldi %cr0, %r7, 0
beq %cr0, 20f
std %r14, 0(%r10)
std %r15, 8(%r10)
std %r16, 16(%r10)
std %r18, 24(%r10)
std %r19, 32(%r10)
std %r20, 40(%r10)
or %r16, %r10, %r10
addi %r16, %r16, 64
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
stxvd2x 32, %r16, %r0
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
lxvd2x 42, %r14, %r0
vperm %v10, %v10, %v10, %v19
ldbrx %r18, %r5, %r0
li %r11, 8
lwbrx %r19, %r5, %r11
rldicr %r19, %r19, 32, 31
li %r11, 12
lwbrx %r8, %r5, %r11
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
22:
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
bne %cr0, 22b
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
cmpldi %cr0, %r7, 0
beq %cr0, 23f
25:
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
li %r12, 4
26:
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
lxvd2x 41, %r15, %r0
vperm %v9, %v9, %v9, %v19
vxor %v9, %v9, %v10
addi %r15, %r15, 16
lxvd2x 48, %r15, %r0
vperm %v16, %v16, %v16, %v19
addi %r15, %r15, 16
vsldoi %v16, %v16, %v16, 8
vsldoi %v18, %v9, %v16, 8
vsldoi %v17, %v16, %v9, 8
vsldoi %v17, %v17, %v17, 8
vpmsumd %v16, %v17, %v12
vpmsumd %v14, %v18, %v11
vpmsumd %v15, %v17, %v11
vpmsumd %v17, %v18, %v12
vxor %v15, %v15, %v17
lxvd2x 49, %r16, %r0
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
addi %r12, %r12, -1
cmpldi %cr0, %r12, 0
bne %cr0, 26b
27:
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
bne %cr0, 27b
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
cmpldi %cr0, %r7, 0
bne %cr0, 25b
b 24f
23:
24:
li %r12, 4
28:
lxvd2x 41, %r15, %r0
vperm %v9, %v9, %v9, %v19
vxor %v9, %v9, %v10
addi %r15, %r15, 16
lxvd2x 48, %r15, %r0
vperm %v16, %v16, %v16, %v19
addi %r15, %r15, 16
vsldoi %v16, %v16, %v16, 8
vsldoi %v18, %v9, %v16, 8
vsldoi %v17, %v16, %v9, 8
vsldoi %v17, %v17, %v17, 8
vpmsumd %v16, %v17, %v12
vpmsumd %v14, %v18, %v11
vpmsumd %v15, %v17, %v11
vpmsumd %v17, %v18, %v12
vxor %v15, %v15, %v17
lxvd2x 49, %r16, %r0
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
addi %r12, %r12, -1
cmpldi %cr0, %r12, 0
bne %cr0, 28b
li %r11, 12
stwbrx %r8, %r5, %r11
vperm %v10, %v10, %v10, %v19
stxvd2x 42, %r14, %r0
addi %r12, %r16, -64
ld %r14, 0(%r12)
ld %r15, 8(%r12)
ld %r16, 16(%r12)
ld %r18, 24(%r12)
ld %r19, 32(%r12)
ld %r20, 40(%r12)
b 21f
20:
21:
blr
