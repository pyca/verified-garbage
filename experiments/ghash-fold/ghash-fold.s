.text
.abiversion 2
.globl gh_base
.type gh_base,@function
gh_base:
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
22:
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
bne %cr0, 22b
vperm %v7, %v0, %v0, %v18
stxvd2x 39, %r4, %r0
b 21f
20:
21:
blr
.globl gh_fold4
.type gh_fold4,@function
gh_fold4:
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
rldicl %r10, %r6, 62, 2
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
24:
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
vxor %v6, %v6, %v0
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v10
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v10
vpmsumd %v4, %v6, %v10
vor %v0, %v3, %v3
vor %v15, %v4, %v4
vor %v17, %v5, %v5
addi %r5, %r5, 16
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v9
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v9
vpmsumd %v4, %v6, %v9
vxor %v0, %v0, %v3
vxor %v15, %v15, %v4
vxor %v17, %v17, %v5
addi %r5, %r5, 16
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v8
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v8
vpmsumd %v4, %v6, %v8
vxor %v0, %v0, %v3
vxor %v15, %v15, %v4
vxor %v17, %v17, %v5
addi %r5, %r5, 16
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v16
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v16
vpmsumd %v4, %v6, %v16
vxor %v3, %v3, %v0
vxor %v4, %v4, %v15
vxor %v5, %v5, %v17
addi %r5, %r5, 16
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
addi %r6, %r6, -4
rldicl %r10, %r6, 62, 2
cmpldi %cr0, %r10, 0
bne %cr0, 24b
b 23f
22:
23:
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
b 21f
20:
21:
blr
.globl gh_fold8
.type gh_fold8,@function
gh_fold8:
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
rldicl %r10, %r6, 61, 3
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
24:
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
vxor %v6, %v6, %v0
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v14
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v14
vpmsumd %v4, %v6, %v14
vor %v0, %v3, %v3
vor %v15, %v4, %v4
vor %v17, %v5, %v5
addi %r5, %r5, 16
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v13
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v13
vpmsumd %v4, %v6, %v13
vxor %v0, %v0, %v3
vxor %v15, %v15, %v4
vxor %v17, %v17, %v5
addi %r5, %r5, 16
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v12
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v12
vpmsumd %v4, %v6, %v12
vxor %v0, %v0, %v3
vxor %v15, %v15, %v4
vxor %v17, %v17, %v5
addi %r5, %r5, 16
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v11
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v11
vpmsumd %v4, %v6, %v11
vxor %v0, %v0, %v3
vxor %v15, %v15, %v4
vxor %v17, %v17, %v5
addi %r5, %r5, 16
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v10
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v10
vpmsumd %v4, %v6, %v10
vxor %v0, %v0, %v3
vxor %v15, %v15, %v4
vxor %v17, %v17, %v5
addi %r5, %r5, 16
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v9
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v9
vpmsumd %v4, %v6, %v9
vxor %v0, %v0, %v3
vxor %v15, %v15, %v4
vxor %v17, %v17, %v5
addi %r5, %r5, 16
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v8
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v8
vpmsumd %v4, %v6, %v8
vxor %v0, %v0, %v3
vxor %v15, %v15, %v4
vxor %v17, %v17, %v5
addi %r5, %r5, 16
lxvd2x 38, %r5, %r0
vperm %v6, %v6, %v6, %v18
vsldoi %v2, %v6, %v19, 8
vpmsumd %v5, %v2, %v16
vsldoi %v2, %v19, %v6, 8
vpmsumd %v3, %v2, %v16
vpmsumd %v4, %v6, %v16
vxor %v3, %v3, %v0
vxor %v4, %v4, %v15
vxor %v5, %v5, %v17
addi %r5, %r5, 16
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
b 23f
22:
23:
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
b 21f
20:
21:
blr
