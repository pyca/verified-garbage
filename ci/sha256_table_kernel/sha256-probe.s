.text
.abiversion 2
.globl sha_scalar
.type sha_scalar,@function
sha_scalar:
std %r14, 64(%r6)
std %r15, 72(%r6)
std %r16, 80(%r6)
std %r17, 88(%r6)
std %r18, 96(%r6)
std %r19, 104(%r6)
cmpldi %cr0, %r5, 0
beq %cr0, 20f
22:
lwz %r7, 0(%r3)
lwz %r8, 4(%r3)
lwz %r9, 8(%r3)
lwz %r10, 12(%r3)
lwz %r11, 16(%r3)
lwz %r12, 20(%r3)
lwz %r14, 24(%r3)
lwz %r15, 28(%r3)
li %r0, 0
lwbrx %r16, %r4, %r0
stw %r16, 0(%r6)
lis %r17, 17034
ori %r17, %r17, 12184
add %r17, %r17, %r16
add %r15, %r15, %r17
rlwinm %r17, %r11, 26, 0, 31
rlwinm %r18, %r11, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 7, 0, 31
xor %r17, %r17, %r18
add %r15, %r15, %r17
xor %r17, %r12, %r14
and %r17, %r17, %r11
xor %r17, %r17, %r14
add %r15, %r15, %r17
add %r10, %r10, %r15
rlwinm %r17, %r7, 30, 0, 31
rlwinm %r18, %r7, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r7, %r8
and %r18, %r18, %r9
and %r19, %r7, %r8
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r15, %r15, %r17
li %r0, 4
lwbrx %r16, %r4, %r0
stw %r16, 4(%r6)
lis %r17, 28983
ori %r17, %r17, 17553
add %r17, %r17, %r16
add %r14, %r14, %r17
rlwinm %r17, %r10, 26, 0, 31
rlwinm %r18, %r10, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 7, 0, 31
xor %r17, %r17, %r18
add %r14, %r14, %r17
xor %r17, %r11, %r12
and %r17, %r17, %r10
xor %r17, %r17, %r12
add %r14, %r14, %r17
add %r9, %r9, %r14
rlwinm %r17, %r15, 30, 0, 31
rlwinm %r18, %r15, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r15, %r7
and %r18, %r18, %r8
and %r19, %r15, %r7
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r14, %r14, %r17
li %r0, 8
lwbrx %r16, %r4, %r0
stw %r16, 8(%r6)
lis %r17, -19008
ori %r17, %r17, 64463
add %r17, %r17, %r16
add %r12, %r12, %r17
rlwinm %r17, %r9, 26, 0, 31
rlwinm %r18, %r9, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 7, 0, 31
xor %r17, %r17, %r18
add %r12, %r12, %r17
xor %r17, %r10, %r11
and %r17, %r17, %r9
xor %r17, %r17, %r11
add %r12, %r12, %r17
add %r8, %r8, %r12
rlwinm %r17, %r14, 30, 0, 31
rlwinm %r18, %r14, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r14, %r15
and %r18, %r18, %r7
and %r19, %r14, %r15
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r12, %r12, %r17
li %r0, 12
lwbrx %r16, %r4, %r0
stw %r16, 12(%r6)
lis %r17, -5707
ori %r17, %r17, 56229
add %r17, %r17, %r16
add %r11, %r11, %r17
rlwinm %r17, %r8, 26, 0, 31
rlwinm %r18, %r8, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 7, 0, 31
xor %r17, %r17, %r18
add %r11, %r11, %r17
xor %r17, %r9, %r10
and %r17, %r17, %r8
xor %r17, %r17, %r10
add %r11, %r11, %r17
add %r7, %r7, %r11
rlwinm %r17, %r12, 30, 0, 31
rlwinm %r18, %r12, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r12, %r14
and %r18, %r18, %r15
and %r19, %r12, %r14
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r11, %r11, %r17
li %r0, 16
lwbrx %r16, %r4, %r0
stw %r16, 16(%r6)
lis %r17, 14678
ori %r17, %r17, 49755
add %r17, %r17, %r16
add %r10, %r10, %r17
rlwinm %r17, %r7, 26, 0, 31
rlwinm %r18, %r7, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 7, 0, 31
xor %r17, %r17, %r18
add %r10, %r10, %r17
xor %r17, %r8, %r9
and %r17, %r17, %r7
xor %r17, %r17, %r9
add %r10, %r10, %r17
add %r15, %r15, %r10
rlwinm %r17, %r11, 30, 0, 31
rlwinm %r18, %r11, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r11, %r12
and %r18, %r18, %r14
and %r19, %r11, %r12
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r10, %r10, %r17
li %r0, 20
lwbrx %r16, %r4, %r0
stw %r16, 20(%r6)
lis %r17, 23025
ori %r17, %r17, 4593
add %r17, %r17, %r16
add %r9, %r9, %r17
rlwinm %r17, %r15, 26, 0, 31
rlwinm %r18, %r15, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 7, 0, 31
xor %r17, %r17, %r18
add %r9, %r9, %r17
xor %r17, %r7, %r8
and %r17, %r17, %r15
xor %r17, %r17, %r8
add %r9, %r9, %r17
add %r14, %r14, %r9
rlwinm %r17, %r10, 30, 0, 31
rlwinm %r18, %r10, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r10, %r11
and %r18, %r18, %r12
and %r19, %r10, %r11
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r9, %r9, %r17
li %r0, 24
lwbrx %r16, %r4, %r0
stw %r16, 24(%r6)
lis %r17, -28097
ori %r17, %r17, 33444
add %r17, %r17, %r16
add %r8, %r8, %r17
rlwinm %r17, %r14, 26, 0, 31
rlwinm %r18, %r14, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 7, 0, 31
xor %r17, %r17, %r18
add %r8, %r8, %r17
xor %r17, %r15, %r7
and %r17, %r17, %r14
xor %r17, %r17, %r7
add %r8, %r8, %r17
add %r12, %r12, %r8
rlwinm %r17, %r9, 30, 0, 31
rlwinm %r18, %r9, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r9, %r10
and %r18, %r18, %r11
and %r19, %r9, %r10
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r8, %r8, %r17
li %r0, 28
lwbrx %r16, %r4, %r0
stw %r16, 28(%r6)
lis %r17, -21732
ori %r17, %r17, 24277
add %r17, %r17, %r16
add %r7, %r7, %r17
rlwinm %r17, %r12, 26, 0, 31
rlwinm %r18, %r12, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 7, 0, 31
xor %r17, %r17, %r18
add %r7, %r7, %r17
xor %r17, %r14, %r15
and %r17, %r17, %r12
xor %r17, %r17, %r15
add %r7, %r7, %r17
add %r11, %r11, %r7
rlwinm %r17, %r8, 30, 0, 31
rlwinm %r18, %r8, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r8, %r9
and %r18, %r18, %r10
and %r19, %r8, %r9
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r7, %r7, %r17
li %r0, 32
lwbrx %r16, %r4, %r0
stw %r16, 32(%r6)
lis %r17, -10233
ori %r17, %r17, 43672
add %r17, %r17, %r16
add %r15, %r15, %r17
rlwinm %r17, %r11, 26, 0, 31
rlwinm %r18, %r11, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 7, 0, 31
xor %r17, %r17, %r18
add %r15, %r15, %r17
xor %r17, %r12, %r14
and %r17, %r17, %r11
xor %r17, %r17, %r14
add %r15, %r15, %r17
add %r10, %r10, %r15
rlwinm %r17, %r7, 30, 0, 31
rlwinm %r18, %r7, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r7, %r8
and %r18, %r18, %r9
and %r19, %r7, %r8
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r15, %r15, %r17
li %r0, 36
lwbrx %r16, %r4, %r0
stw %r16, 36(%r6)
lis %r17, 4739
ori %r17, %r17, 23297
add %r17, %r17, %r16
add %r14, %r14, %r17
rlwinm %r17, %r10, 26, 0, 31
rlwinm %r18, %r10, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 7, 0, 31
xor %r17, %r17, %r18
add %r14, %r14, %r17
xor %r17, %r11, %r12
and %r17, %r17, %r10
xor %r17, %r17, %r12
add %r14, %r14, %r17
add %r9, %r9, %r14
rlwinm %r17, %r15, 30, 0, 31
rlwinm %r18, %r15, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r15, %r7
and %r18, %r18, %r8
and %r19, %r15, %r7
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r14, %r14, %r17
li %r0, 40
lwbrx %r16, %r4, %r0
stw %r16, 40(%r6)
lis %r17, 9265
ori %r17, %r17, 34238
add %r17, %r17, %r16
add %r12, %r12, %r17
rlwinm %r17, %r9, 26, 0, 31
rlwinm %r18, %r9, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 7, 0, 31
xor %r17, %r17, %r18
add %r12, %r12, %r17
xor %r17, %r10, %r11
and %r17, %r17, %r9
xor %r17, %r17, %r11
add %r12, %r12, %r17
add %r8, %r8, %r12
rlwinm %r17, %r14, 30, 0, 31
rlwinm %r18, %r14, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r14, %r15
and %r18, %r18, %r7
and %r19, %r14, %r15
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r12, %r12, %r17
li %r0, 44
lwbrx %r16, %r4, %r0
stw %r16, 44(%r6)
lis %r17, 21772
ori %r17, %r17, 32195
add %r17, %r17, %r16
add %r11, %r11, %r17
rlwinm %r17, %r8, 26, 0, 31
rlwinm %r18, %r8, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 7, 0, 31
xor %r17, %r17, %r18
add %r11, %r11, %r17
xor %r17, %r9, %r10
and %r17, %r17, %r8
xor %r17, %r17, %r10
add %r11, %r11, %r17
add %r7, %r7, %r11
rlwinm %r17, %r12, 30, 0, 31
rlwinm %r18, %r12, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r12, %r14
and %r18, %r18, %r15
and %r19, %r12, %r14
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r11, %r11, %r17
li %r0, 48
lwbrx %r16, %r4, %r0
stw %r16, 48(%r6)
lis %r17, 29374
ori %r17, %r17, 23924
add %r17, %r17, %r16
add %r10, %r10, %r17
rlwinm %r17, %r7, 26, 0, 31
rlwinm %r18, %r7, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 7, 0, 31
xor %r17, %r17, %r18
add %r10, %r10, %r17
xor %r17, %r8, %r9
and %r17, %r17, %r7
xor %r17, %r17, %r9
add %r10, %r10, %r17
add %r15, %r15, %r10
rlwinm %r17, %r11, 30, 0, 31
rlwinm %r18, %r11, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r11, %r12
and %r18, %r18, %r14
and %r19, %r11, %r12
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r10, %r10, %r17
li %r0, 52
lwbrx %r16, %r4, %r0
stw %r16, 52(%r6)
lis %r17, -32546
ori %r17, %r17, 45566
add %r17, %r17, %r16
add %r9, %r9, %r17
rlwinm %r17, %r15, 26, 0, 31
rlwinm %r18, %r15, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 7, 0, 31
xor %r17, %r17, %r18
add %r9, %r9, %r17
xor %r17, %r7, %r8
and %r17, %r17, %r15
xor %r17, %r17, %r8
add %r9, %r9, %r17
add %r14, %r14, %r9
rlwinm %r17, %r10, 30, 0, 31
rlwinm %r18, %r10, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r10, %r11
and %r18, %r18, %r12
and %r19, %r10, %r11
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r9, %r9, %r17
li %r0, 56
lwbrx %r16, %r4, %r0
stw %r16, 56(%r6)
lis %r17, -25636
ori %r17, %r17, 1703
add %r17, %r17, %r16
add %r8, %r8, %r17
rlwinm %r17, %r14, 26, 0, 31
rlwinm %r18, %r14, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 7, 0, 31
xor %r17, %r17, %r18
add %r8, %r8, %r17
xor %r17, %r15, %r7
and %r17, %r17, %r14
xor %r17, %r17, %r7
add %r8, %r8, %r17
add %r12, %r12, %r8
rlwinm %r17, %r9, 30, 0, 31
rlwinm %r18, %r9, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r9, %r10
and %r18, %r18, %r11
and %r19, %r9, %r10
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r8, %r8, %r17
li %r0, 60
lwbrx %r16, %r4, %r0
stw %r16, 60(%r6)
lis %r17, -15973
ori %r17, %r17, 61812
add %r17, %r17, %r16
add %r7, %r7, %r17
rlwinm %r17, %r12, 26, 0, 31
rlwinm %r18, %r12, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 7, 0, 31
xor %r17, %r17, %r18
add %r7, %r7, %r17
xor %r17, %r14, %r15
and %r17, %r17, %r12
xor %r17, %r17, %r15
add %r7, %r7, %r17
add %r11, %r11, %r7
rlwinm %r17, %r8, 30, 0, 31
rlwinm %r18, %r8, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r8, %r9
and %r18, %r18, %r10
and %r19, %r8, %r9
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r7, %r7, %r17
lwz %r17, 56(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 36(%r6)
add %r16, %r16, %r18
lwz %r17, 4(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 0(%r6)
add %r16, %r16, %r18
stw %r16, 0(%r6)
lis %r17, -7013
ori %r17, %r17, 27073
add %r17, %r17, %r16
add %r15, %r15, %r17
rlwinm %r17, %r11, 26, 0, 31
rlwinm %r18, %r11, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 7, 0, 31
xor %r17, %r17, %r18
add %r15, %r15, %r17
xor %r17, %r12, %r14
and %r17, %r17, %r11
xor %r17, %r17, %r14
add %r15, %r15, %r17
add %r10, %r10, %r15
rlwinm %r17, %r7, 30, 0, 31
rlwinm %r18, %r7, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r7, %r8
and %r18, %r18, %r9
and %r19, %r7, %r8
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r15, %r15, %r17
lwz %r17, 60(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 40(%r6)
add %r16, %r16, %r18
lwz %r17, 8(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 4(%r6)
add %r16, %r16, %r18
stw %r16, 4(%r6)
lis %r17, -4162
ori %r17, %r17, 18310
add %r17, %r17, %r16
add %r14, %r14, %r17
rlwinm %r17, %r10, 26, 0, 31
rlwinm %r18, %r10, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 7, 0, 31
xor %r17, %r17, %r18
add %r14, %r14, %r17
xor %r17, %r11, %r12
and %r17, %r17, %r10
xor %r17, %r17, %r12
add %r14, %r14, %r17
add %r9, %r9, %r14
rlwinm %r17, %r15, 30, 0, 31
rlwinm %r18, %r15, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r15, %r7
and %r18, %r18, %r8
and %r19, %r15, %r7
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r14, %r14, %r17
lwz %r17, 0(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 44(%r6)
add %r16, %r16, %r18
lwz %r17, 12(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 8(%r6)
add %r16, %r16, %r18
stw %r16, 8(%r6)
lis %r17, 4033
ori %r17, %r17, 40390
add %r17, %r17, %r16
add %r12, %r12, %r17
rlwinm %r17, %r9, 26, 0, 31
rlwinm %r18, %r9, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 7, 0, 31
xor %r17, %r17, %r18
add %r12, %r12, %r17
xor %r17, %r10, %r11
and %r17, %r17, %r9
xor %r17, %r17, %r11
add %r12, %r12, %r17
add %r8, %r8, %r12
rlwinm %r17, %r14, 30, 0, 31
rlwinm %r18, %r14, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r14, %r15
and %r18, %r18, %r7
and %r19, %r14, %r15
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r12, %r12, %r17
lwz %r17, 4(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 48(%r6)
add %r16, %r16, %r18
lwz %r17, 16(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 12(%r6)
add %r16, %r16, %r18
stw %r16, 12(%r6)
lis %r17, 9228
ori %r17, %r17, 41420
add %r17, %r17, %r16
add %r11, %r11, %r17
rlwinm %r17, %r8, 26, 0, 31
rlwinm %r18, %r8, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 7, 0, 31
xor %r17, %r17, %r18
add %r11, %r11, %r17
xor %r17, %r9, %r10
and %r17, %r17, %r8
xor %r17, %r17, %r10
add %r11, %r11, %r17
add %r7, %r7, %r11
rlwinm %r17, %r12, 30, 0, 31
rlwinm %r18, %r12, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r12, %r14
and %r18, %r18, %r15
and %r19, %r12, %r14
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r11, %r11, %r17
lwz %r17, 8(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 52(%r6)
add %r16, %r16, %r18
lwz %r17, 20(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 16(%r6)
add %r16, %r16, %r18
stw %r16, 16(%r6)
lis %r17, 11753
ori %r17, %r17, 11375
add %r17, %r17, %r16
add %r10, %r10, %r17
rlwinm %r17, %r7, 26, 0, 31
rlwinm %r18, %r7, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 7, 0, 31
xor %r17, %r17, %r18
add %r10, %r10, %r17
xor %r17, %r8, %r9
and %r17, %r17, %r7
xor %r17, %r17, %r9
add %r10, %r10, %r17
add %r15, %r15, %r10
rlwinm %r17, %r11, 30, 0, 31
rlwinm %r18, %r11, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r11, %r12
and %r18, %r18, %r14
and %r19, %r11, %r12
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r10, %r10, %r17
lwz %r17, 12(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 56(%r6)
add %r16, %r16, %r18
lwz %r17, 24(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 20(%r6)
add %r16, %r16, %r18
stw %r16, 20(%r6)
lis %r17, 19060
ori %r17, %r17, 33962
add %r17, %r17, %r16
add %r9, %r9, %r17
rlwinm %r17, %r15, 26, 0, 31
rlwinm %r18, %r15, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 7, 0, 31
xor %r17, %r17, %r18
add %r9, %r9, %r17
xor %r17, %r7, %r8
and %r17, %r17, %r15
xor %r17, %r17, %r8
add %r9, %r9, %r17
add %r14, %r14, %r9
rlwinm %r17, %r10, 30, 0, 31
rlwinm %r18, %r10, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r10, %r11
and %r18, %r18, %r12
and %r19, %r10, %r11
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r9, %r9, %r17
lwz %r17, 16(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 60(%r6)
add %r16, %r16, %r18
lwz %r17, 28(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 24(%r6)
add %r16, %r16, %r18
stw %r16, 24(%r6)
lis %r17, 23728
ori %r17, %r17, 43484
add %r17, %r17, %r16
add %r8, %r8, %r17
rlwinm %r17, %r14, 26, 0, 31
rlwinm %r18, %r14, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 7, 0, 31
xor %r17, %r17, %r18
add %r8, %r8, %r17
xor %r17, %r15, %r7
and %r17, %r17, %r14
xor %r17, %r17, %r7
add %r8, %r8, %r17
add %r12, %r12, %r8
rlwinm %r17, %r9, 30, 0, 31
rlwinm %r18, %r9, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r9, %r10
and %r18, %r18, %r11
and %r19, %r9, %r10
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r8, %r8, %r17
lwz %r17, 20(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 0(%r6)
add %r16, %r16, %r18
lwz %r17, 32(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 28(%r6)
add %r16, %r16, %r18
stw %r16, 28(%r6)
lis %r17, 30457
ori %r17, %r17, 35034
add %r17, %r17, %r16
add %r7, %r7, %r17
rlwinm %r17, %r12, 26, 0, 31
rlwinm %r18, %r12, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 7, 0, 31
xor %r17, %r17, %r18
add %r7, %r7, %r17
xor %r17, %r14, %r15
and %r17, %r17, %r12
xor %r17, %r17, %r15
add %r7, %r7, %r17
add %r11, %r11, %r7
rlwinm %r17, %r8, 30, 0, 31
rlwinm %r18, %r8, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r8, %r9
and %r18, %r18, %r10
and %r19, %r8, %r9
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r7, %r7, %r17
lwz %r17, 24(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 4(%r6)
add %r16, %r16, %r18
lwz %r17, 36(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 32(%r6)
add %r16, %r16, %r18
stw %r16, 32(%r6)
lis %r17, -26562
ori %r17, %r17, 20818
add %r17, %r17, %r16
add %r15, %r15, %r17
rlwinm %r17, %r11, 26, 0, 31
rlwinm %r18, %r11, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 7, 0, 31
xor %r17, %r17, %r18
add %r15, %r15, %r17
xor %r17, %r12, %r14
and %r17, %r17, %r11
xor %r17, %r17, %r14
add %r15, %r15, %r17
add %r10, %r10, %r15
rlwinm %r17, %r7, 30, 0, 31
rlwinm %r18, %r7, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r7, %r8
and %r18, %r18, %r9
and %r19, %r7, %r8
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r15, %r15, %r17
lwz %r17, 28(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 8(%r6)
add %r16, %r16, %r18
lwz %r17, 40(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 36(%r6)
add %r16, %r16, %r18
stw %r16, 36(%r6)
lis %r17, -22479
ori %r17, %r17, 50797
add %r17, %r17, %r16
add %r14, %r14, %r17
rlwinm %r17, %r10, 26, 0, 31
rlwinm %r18, %r10, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 7, 0, 31
xor %r17, %r17, %r18
add %r14, %r14, %r17
xor %r17, %r11, %r12
and %r17, %r17, %r10
xor %r17, %r17, %r12
add %r14, %r14, %r17
add %r9, %r9, %r14
rlwinm %r17, %r15, 30, 0, 31
rlwinm %r18, %r15, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r15, %r7
and %r18, %r18, %r8
and %r19, %r15, %r7
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r14, %r14, %r17
lwz %r17, 32(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 12(%r6)
add %r16, %r16, %r18
lwz %r17, 44(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 40(%r6)
add %r16, %r16, %r18
stw %r16, 40(%r6)
lis %r17, -20477
ori %r17, %r17, 10184
add %r17, %r17, %r16
add %r12, %r12, %r17
rlwinm %r17, %r9, 26, 0, 31
rlwinm %r18, %r9, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 7, 0, 31
xor %r17, %r17, %r18
add %r12, %r12, %r17
xor %r17, %r10, %r11
and %r17, %r17, %r9
xor %r17, %r17, %r11
add %r12, %r12, %r17
add %r8, %r8, %r12
rlwinm %r17, %r14, 30, 0, 31
rlwinm %r18, %r14, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r14, %r15
and %r18, %r18, %r7
and %r19, %r14, %r15
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r12, %r12, %r17
lwz %r17, 36(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 16(%r6)
add %r16, %r16, %r18
lwz %r17, 48(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 44(%r6)
add %r16, %r16, %r18
stw %r16, 44(%r6)
lis %r17, -16551
ori %r17, %r17, 32711
add %r17, %r17, %r16
add %r11, %r11, %r17
rlwinm %r17, %r8, 26, 0, 31
rlwinm %r18, %r8, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 7, 0, 31
xor %r17, %r17, %r18
add %r11, %r11, %r17
xor %r17, %r9, %r10
and %r17, %r17, %r8
xor %r17, %r17, %r10
add %r11, %r11, %r17
add %r7, %r7, %r11
rlwinm %r17, %r12, 30, 0, 31
rlwinm %r18, %r12, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r12, %r14
and %r18, %r18, %r15
and %r19, %r12, %r14
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r11, %r11, %r17
lwz %r17, 40(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 20(%r6)
add %r16, %r16, %r18
lwz %r17, 52(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 48(%r6)
add %r16, %r16, %r18
stw %r16, 48(%r6)
lis %r17, -14624
ori %r17, %r17, 3059
add %r17, %r17, %r16
add %r10, %r10, %r17
rlwinm %r17, %r7, 26, 0, 31
rlwinm %r18, %r7, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 7, 0, 31
xor %r17, %r17, %r18
add %r10, %r10, %r17
xor %r17, %r8, %r9
and %r17, %r17, %r7
xor %r17, %r17, %r9
add %r10, %r10, %r17
add %r15, %r15, %r10
rlwinm %r17, %r11, 30, 0, 31
rlwinm %r18, %r11, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r11, %r12
and %r18, %r18, %r14
and %r19, %r11, %r12
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r10, %r10, %r17
lwz %r17, 44(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 24(%r6)
add %r16, %r16, %r18
lwz %r17, 56(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 52(%r6)
add %r16, %r16, %r18
stw %r16, 52(%r6)
lis %r17, -10841
ori %r17, %r17, 37191
add %r17, %r17, %r16
add %r9, %r9, %r17
rlwinm %r17, %r15, 26, 0, 31
rlwinm %r18, %r15, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 7, 0, 31
xor %r17, %r17, %r18
add %r9, %r9, %r17
xor %r17, %r7, %r8
and %r17, %r17, %r15
xor %r17, %r17, %r8
add %r9, %r9, %r17
add %r14, %r14, %r9
rlwinm %r17, %r10, 30, 0, 31
rlwinm %r18, %r10, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r10, %r11
and %r18, %r18, %r12
and %r19, %r10, %r11
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r9, %r9, %r17
lwz %r17, 48(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 28(%r6)
add %r16, %r16, %r18
lwz %r17, 60(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 56(%r6)
add %r16, %r16, %r18
stw %r16, 56(%r6)
lis %r17, 1738
ori %r17, %r17, 25425
add %r17, %r17, %r16
add %r8, %r8, %r17
rlwinm %r17, %r14, 26, 0, 31
rlwinm %r18, %r14, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 7, 0, 31
xor %r17, %r17, %r18
add %r8, %r8, %r17
xor %r17, %r15, %r7
and %r17, %r17, %r14
xor %r17, %r17, %r7
add %r8, %r8, %r17
add %r12, %r12, %r8
rlwinm %r17, %r9, 30, 0, 31
rlwinm %r18, %r9, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r9, %r10
and %r18, %r18, %r11
and %r19, %r9, %r10
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r8, %r8, %r17
lwz %r17, 52(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 32(%r6)
add %r16, %r16, %r18
lwz %r17, 0(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 60(%r6)
add %r16, %r16, %r18
stw %r16, 60(%r6)
lis %r17, 5161
ori %r17, %r17, 10599
add %r17, %r17, %r16
add %r7, %r7, %r17
rlwinm %r17, %r12, 26, 0, 31
rlwinm %r18, %r12, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 7, 0, 31
xor %r17, %r17, %r18
add %r7, %r7, %r17
xor %r17, %r14, %r15
and %r17, %r17, %r12
xor %r17, %r17, %r15
add %r7, %r7, %r17
add %r11, %r11, %r7
rlwinm %r17, %r8, 30, 0, 31
rlwinm %r18, %r8, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r8, %r9
and %r18, %r18, %r10
and %r19, %r8, %r9
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r7, %r7, %r17
lwz %r17, 56(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 36(%r6)
add %r16, %r16, %r18
lwz %r17, 4(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 0(%r6)
add %r16, %r16, %r18
stw %r16, 0(%r6)
lis %r17, 10167
ori %r17, %r17, 2693
add %r17, %r17, %r16
add %r15, %r15, %r17
rlwinm %r17, %r11, 26, 0, 31
rlwinm %r18, %r11, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 7, 0, 31
xor %r17, %r17, %r18
add %r15, %r15, %r17
xor %r17, %r12, %r14
and %r17, %r17, %r11
xor %r17, %r17, %r14
add %r15, %r15, %r17
add %r10, %r10, %r15
rlwinm %r17, %r7, 30, 0, 31
rlwinm %r18, %r7, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r7, %r8
and %r18, %r18, %r9
and %r19, %r7, %r8
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r15, %r15, %r17
lwz %r17, 60(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 40(%r6)
add %r16, %r16, %r18
lwz %r17, 8(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 4(%r6)
add %r16, %r16, %r18
stw %r16, 4(%r6)
lis %r17, 11803
ori %r17, %r17, 8504
add %r17, %r17, %r16
add %r14, %r14, %r17
rlwinm %r17, %r10, 26, 0, 31
rlwinm %r18, %r10, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 7, 0, 31
xor %r17, %r17, %r18
add %r14, %r14, %r17
xor %r17, %r11, %r12
and %r17, %r17, %r10
xor %r17, %r17, %r12
add %r14, %r14, %r17
add %r9, %r9, %r14
rlwinm %r17, %r15, 30, 0, 31
rlwinm %r18, %r15, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r15, %r7
and %r18, %r18, %r8
and %r19, %r15, %r7
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r14, %r14, %r17
lwz %r17, 0(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 44(%r6)
add %r16, %r16, %r18
lwz %r17, 12(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 8(%r6)
add %r16, %r16, %r18
stw %r16, 8(%r6)
lis %r17, 19756
ori %r17, %r17, 28156
add %r17, %r17, %r16
add %r12, %r12, %r17
rlwinm %r17, %r9, 26, 0, 31
rlwinm %r18, %r9, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 7, 0, 31
xor %r17, %r17, %r18
add %r12, %r12, %r17
xor %r17, %r10, %r11
and %r17, %r17, %r9
xor %r17, %r17, %r11
add %r12, %r12, %r17
add %r8, %r8, %r12
rlwinm %r17, %r14, 30, 0, 31
rlwinm %r18, %r14, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r14, %r15
and %r18, %r18, %r7
and %r19, %r14, %r15
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r12, %r12, %r17
lwz %r17, 4(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 48(%r6)
add %r16, %r16, %r18
lwz %r17, 16(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 12(%r6)
add %r16, %r16, %r18
stw %r16, 12(%r6)
lis %r17, 21304
ori %r17, %r17, 3347
add %r17, %r17, %r16
add %r11, %r11, %r17
rlwinm %r17, %r8, 26, 0, 31
rlwinm %r18, %r8, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 7, 0, 31
xor %r17, %r17, %r18
add %r11, %r11, %r17
xor %r17, %r9, %r10
and %r17, %r17, %r8
xor %r17, %r17, %r10
add %r11, %r11, %r17
add %r7, %r7, %r11
rlwinm %r17, %r12, 30, 0, 31
rlwinm %r18, %r12, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r12, %r14
and %r18, %r18, %r15
and %r19, %r12, %r14
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r11, %r11, %r17
lwz %r17, 8(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 52(%r6)
add %r16, %r16, %r18
lwz %r17, 20(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 16(%r6)
add %r16, %r16, %r18
stw %r16, 16(%r6)
lis %r17, 25866
ori %r17, %r17, 29524
add %r17, %r17, %r16
add %r10, %r10, %r17
rlwinm %r17, %r7, 26, 0, 31
rlwinm %r18, %r7, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 7, 0, 31
xor %r17, %r17, %r18
add %r10, %r10, %r17
xor %r17, %r8, %r9
and %r17, %r17, %r7
xor %r17, %r17, %r9
add %r10, %r10, %r17
add %r15, %r15, %r10
rlwinm %r17, %r11, 30, 0, 31
rlwinm %r18, %r11, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r11, %r12
and %r18, %r18, %r14
and %r19, %r11, %r12
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r10, %r10, %r17
lwz %r17, 12(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 56(%r6)
add %r16, %r16, %r18
lwz %r17, 24(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 20(%r6)
add %r16, %r16, %r18
stw %r16, 20(%r6)
lis %r17, 30314
ori %r17, %r17, 2747
add %r17, %r17, %r16
add %r9, %r9, %r17
rlwinm %r17, %r15, 26, 0, 31
rlwinm %r18, %r15, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 7, 0, 31
xor %r17, %r17, %r18
add %r9, %r9, %r17
xor %r17, %r7, %r8
and %r17, %r17, %r15
xor %r17, %r17, %r8
add %r9, %r9, %r17
add %r14, %r14, %r9
rlwinm %r17, %r10, 30, 0, 31
rlwinm %r18, %r10, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r10, %r11
and %r18, %r18, %r12
and %r19, %r10, %r11
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r9, %r9, %r17
lwz %r17, 16(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 60(%r6)
add %r16, %r16, %r18
lwz %r17, 28(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 24(%r6)
add %r16, %r16, %r18
stw %r16, 24(%r6)
lis %r17, -32318
ori %r17, %r17, 51502
add %r17, %r17, %r16
add %r8, %r8, %r17
rlwinm %r17, %r14, 26, 0, 31
rlwinm %r18, %r14, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 7, 0, 31
xor %r17, %r17, %r18
add %r8, %r8, %r17
xor %r17, %r15, %r7
and %r17, %r17, %r14
xor %r17, %r17, %r7
add %r8, %r8, %r17
add %r12, %r12, %r8
rlwinm %r17, %r9, 30, 0, 31
rlwinm %r18, %r9, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r9, %r10
and %r18, %r18, %r11
and %r19, %r9, %r10
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r8, %r8, %r17
lwz %r17, 20(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 0(%r6)
add %r16, %r16, %r18
lwz %r17, 32(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 28(%r6)
add %r16, %r16, %r18
stw %r16, 28(%r6)
lis %r17, -28046
ori %r17, %r17, 11397
add %r17, %r17, %r16
add %r7, %r7, %r17
rlwinm %r17, %r12, 26, 0, 31
rlwinm %r18, %r12, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 7, 0, 31
xor %r17, %r17, %r18
add %r7, %r7, %r17
xor %r17, %r14, %r15
and %r17, %r17, %r12
xor %r17, %r17, %r15
add %r7, %r7, %r17
add %r11, %r11, %r7
rlwinm %r17, %r8, 30, 0, 31
rlwinm %r18, %r8, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r8, %r9
and %r18, %r18, %r10
and %r19, %r8, %r9
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r7, %r7, %r17
lwz %r17, 24(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 4(%r6)
add %r16, %r16, %r18
lwz %r17, 36(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 32(%r6)
add %r16, %r16, %r18
stw %r16, 32(%r6)
lis %r17, -23873
ori %r17, %r17, 59553
add %r17, %r17, %r16
add %r15, %r15, %r17
rlwinm %r17, %r11, 26, 0, 31
rlwinm %r18, %r11, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 7, 0, 31
xor %r17, %r17, %r18
add %r15, %r15, %r17
xor %r17, %r12, %r14
and %r17, %r17, %r11
xor %r17, %r17, %r14
add %r15, %r15, %r17
add %r10, %r10, %r15
rlwinm %r17, %r7, 30, 0, 31
rlwinm %r18, %r7, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r7, %r8
and %r18, %r18, %r9
and %r19, %r7, %r8
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r15, %r15, %r17
lwz %r17, 28(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 8(%r6)
add %r16, %r16, %r18
lwz %r17, 40(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 36(%r6)
add %r16, %r16, %r18
stw %r16, 36(%r6)
lis %r17, -22502
ori %r17, %r17, 26187
add %r17, %r17, %r16
add %r14, %r14, %r17
rlwinm %r17, %r10, 26, 0, 31
rlwinm %r18, %r10, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 7, 0, 31
xor %r17, %r17, %r18
add %r14, %r14, %r17
xor %r17, %r11, %r12
and %r17, %r17, %r10
xor %r17, %r17, %r12
add %r14, %r14, %r17
add %r9, %r9, %r14
rlwinm %r17, %r15, 30, 0, 31
rlwinm %r18, %r15, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r15, %r7
and %r18, %r18, %r8
and %r19, %r15, %r7
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r14, %r14, %r17
lwz %r17, 32(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 12(%r6)
add %r16, %r16, %r18
lwz %r17, 44(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 40(%r6)
add %r16, %r16, %r18
stw %r16, 40(%r6)
lis %r17, -15797
ori %r17, %r17, 35696
add %r17, %r17, %r16
add %r12, %r12, %r17
rlwinm %r17, %r9, 26, 0, 31
rlwinm %r18, %r9, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 7, 0, 31
xor %r17, %r17, %r18
add %r12, %r12, %r17
xor %r17, %r10, %r11
and %r17, %r17, %r9
xor %r17, %r17, %r11
add %r12, %r12, %r17
add %r8, %r8, %r12
rlwinm %r17, %r14, 30, 0, 31
rlwinm %r18, %r14, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r14, %r15
and %r18, %r18, %r7
and %r19, %r14, %r15
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r12, %r12, %r17
lwz %r17, 36(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 16(%r6)
add %r16, %r16, %r18
lwz %r17, 48(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 44(%r6)
add %r16, %r16, %r18
stw %r16, 44(%r6)
lis %r17, -14484
ori %r17, %r17, 20899
add %r17, %r17, %r16
add %r11, %r11, %r17
rlwinm %r17, %r8, 26, 0, 31
rlwinm %r18, %r8, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 7, 0, 31
xor %r17, %r17, %r18
add %r11, %r11, %r17
xor %r17, %r9, %r10
and %r17, %r17, %r8
xor %r17, %r17, %r10
add %r11, %r11, %r17
add %r7, %r7, %r11
rlwinm %r17, %r12, 30, 0, 31
rlwinm %r18, %r12, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r12, %r14
and %r18, %r18, %r15
and %r19, %r12, %r14
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r11, %r11, %r17
lwz %r17, 40(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 20(%r6)
add %r16, %r16, %r18
lwz %r17, 52(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 48(%r6)
add %r16, %r16, %r18
stw %r16, 48(%r6)
lis %r17, -11886
ori %r17, %r17, 59417
add %r17, %r17, %r16
add %r10, %r10, %r17
rlwinm %r17, %r7, 26, 0, 31
rlwinm %r18, %r7, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 7, 0, 31
xor %r17, %r17, %r18
add %r10, %r10, %r17
xor %r17, %r8, %r9
and %r17, %r17, %r7
xor %r17, %r17, %r9
add %r10, %r10, %r17
add %r15, %r15, %r10
rlwinm %r17, %r11, 30, 0, 31
rlwinm %r18, %r11, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r11, %r12
and %r18, %r18, %r14
and %r19, %r11, %r12
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r10, %r10, %r17
lwz %r17, 44(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 24(%r6)
add %r16, %r16, %r18
lwz %r17, 56(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 52(%r6)
add %r16, %r16, %r18
stw %r16, 52(%r6)
lis %r17, -10599
ori %r17, %r17, 1572
add %r17, %r17, %r16
add %r9, %r9, %r17
rlwinm %r17, %r15, 26, 0, 31
rlwinm %r18, %r15, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 7, 0, 31
xor %r17, %r17, %r18
add %r9, %r9, %r17
xor %r17, %r7, %r8
and %r17, %r17, %r15
xor %r17, %r17, %r8
add %r9, %r9, %r17
add %r14, %r14, %r9
rlwinm %r17, %r10, 30, 0, 31
rlwinm %r18, %r10, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r10, %r11
and %r18, %r18, %r12
and %r19, %r10, %r11
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r9, %r9, %r17
lwz %r17, 48(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 28(%r6)
add %r16, %r16, %r18
lwz %r17, 60(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 56(%r6)
add %r16, %r16, %r18
stw %r16, 56(%r6)
lis %r17, -3058
ori %r17, %r17, 13701
add %r17, %r17, %r16
add %r8, %r8, %r17
rlwinm %r17, %r14, 26, 0, 31
rlwinm %r18, %r14, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 7, 0, 31
xor %r17, %r17, %r18
add %r8, %r8, %r17
xor %r17, %r15, %r7
and %r17, %r17, %r14
xor %r17, %r17, %r7
add %r8, %r8, %r17
add %r12, %r12, %r8
rlwinm %r17, %r9, 30, 0, 31
rlwinm %r18, %r9, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r9, %r10
and %r18, %r18, %r11
and %r19, %r9, %r10
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r8, %r8, %r17
lwz %r17, 52(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 32(%r6)
add %r16, %r16, %r18
lwz %r17, 0(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 60(%r6)
add %r16, %r16, %r18
stw %r16, 60(%r6)
lis %r17, 4202
ori %r17, %r17, 41072
add %r17, %r17, %r16
add %r7, %r7, %r17
rlwinm %r17, %r12, 26, 0, 31
rlwinm %r18, %r12, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 7, 0, 31
xor %r17, %r17, %r18
add %r7, %r7, %r17
xor %r17, %r14, %r15
and %r17, %r17, %r12
xor %r17, %r17, %r15
add %r7, %r7, %r17
add %r11, %r11, %r7
rlwinm %r17, %r8, 30, 0, 31
rlwinm %r18, %r8, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r8, %r9
and %r18, %r18, %r10
and %r19, %r8, %r9
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r7, %r7, %r17
lwz %r17, 56(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 36(%r6)
add %r16, %r16, %r18
lwz %r17, 4(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 0(%r6)
add %r16, %r16, %r18
stw %r16, 0(%r6)
lis %r17, 6564
ori %r17, %r17, 49430
add %r17, %r17, %r16
add %r15, %r15, %r17
rlwinm %r17, %r11, 26, 0, 31
rlwinm %r18, %r11, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 7, 0, 31
xor %r17, %r17, %r18
add %r15, %r15, %r17
xor %r17, %r12, %r14
and %r17, %r17, %r11
xor %r17, %r17, %r14
add %r15, %r15, %r17
add %r10, %r10, %r15
rlwinm %r17, %r7, 30, 0, 31
rlwinm %r18, %r7, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r7, %r8
and %r18, %r18, %r9
and %r19, %r7, %r8
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r15, %r15, %r17
lwz %r17, 60(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 40(%r6)
add %r16, %r16, %r18
lwz %r17, 8(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 4(%r6)
add %r16, %r16, %r18
stw %r16, 4(%r6)
lis %r17, 7735
ori %r17, %r17, 27656
add %r17, %r17, %r16
add %r14, %r14, %r17
rlwinm %r17, %r10, 26, 0, 31
rlwinm %r18, %r10, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 7, 0, 31
xor %r17, %r17, %r18
add %r14, %r14, %r17
xor %r17, %r11, %r12
and %r17, %r17, %r10
xor %r17, %r17, %r12
add %r14, %r14, %r17
add %r9, %r9, %r14
rlwinm %r17, %r15, 30, 0, 31
rlwinm %r18, %r15, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r15, %r7
and %r18, %r18, %r8
and %r19, %r15, %r7
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r14, %r14, %r17
lwz %r17, 0(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 44(%r6)
add %r16, %r16, %r18
lwz %r17, 12(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 8(%r6)
add %r16, %r16, %r18
stw %r16, 8(%r6)
lis %r17, 10056
ori %r17, %r17, 30540
add %r17, %r17, %r16
add %r12, %r12, %r17
rlwinm %r17, %r9, 26, 0, 31
rlwinm %r18, %r9, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 7, 0, 31
xor %r17, %r17, %r18
add %r12, %r12, %r17
xor %r17, %r10, %r11
and %r17, %r17, %r9
xor %r17, %r17, %r11
add %r12, %r12, %r17
add %r8, %r8, %r12
rlwinm %r17, %r14, 30, 0, 31
rlwinm %r18, %r14, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r14, %r15
and %r18, %r18, %r7
and %r19, %r14, %r15
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r12, %r12, %r17
lwz %r17, 4(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 48(%r6)
add %r16, %r16, %r18
lwz %r17, 16(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 12(%r6)
add %r16, %r16, %r18
stw %r16, 12(%r6)
lis %r17, 13488
ori %r17, %r17, 48309
add %r17, %r17, %r16
add %r11, %r11, %r17
rlwinm %r17, %r8, 26, 0, 31
rlwinm %r18, %r8, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 7, 0, 31
xor %r17, %r17, %r18
add %r11, %r11, %r17
xor %r17, %r9, %r10
and %r17, %r17, %r8
xor %r17, %r17, %r10
add %r11, %r11, %r17
add %r7, %r7, %r11
rlwinm %r17, %r12, 30, 0, 31
rlwinm %r18, %r12, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r12, %r14
and %r18, %r18, %r15
and %r19, %r12, %r14
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r11, %r11, %r17
lwz %r17, 8(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 52(%r6)
add %r16, %r16, %r18
lwz %r17, 20(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 16(%r6)
add %r16, %r16, %r18
stw %r16, 16(%r6)
lis %r17, 14620
ori %r17, %r17, 3251
add %r17, %r17, %r16
add %r10, %r10, %r17
rlwinm %r17, %r7, 26, 0, 31
rlwinm %r18, %r7, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 7, 0, 31
xor %r17, %r17, %r18
add %r10, %r10, %r17
xor %r17, %r8, %r9
and %r17, %r17, %r7
xor %r17, %r17, %r9
add %r10, %r10, %r17
add %r15, %r15, %r10
rlwinm %r17, %r11, 30, 0, 31
rlwinm %r18, %r11, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r11, %r12
and %r18, %r18, %r14
and %r19, %r11, %r12
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r10, %r10, %r17
lwz %r17, 12(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 56(%r6)
add %r16, %r16, %r18
lwz %r17, 24(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 20(%r6)
add %r16, %r16, %r18
stw %r16, 20(%r6)
lis %r17, 20184
ori %r17, %r17, 43594
add %r17, %r17, %r16
add %r9, %r9, %r17
rlwinm %r17, %r15, 26, 0, 31
rlwinm %r18, %r15, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 7, 0, 31
xor %r17, %r17, %r18
add %r9, %r9, %r17
xor %r17, %r7, %r8
and %r17, %r17, %r15
xor %r17, %r17, %r8
add %r9, %r9, %r17
add %r14, %r14, %r9
rlwinm %r17, %r10, 30, 0, 31
rlwinm %r18, %r10, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r10, %r11
and %r18, %r18, %r12
and %r19, %r10, %r11
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r9, %r9, %r17
lwz %r17, 16(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 60(%r6)
add %r16, %r16, %r18
lwz %r17, 28(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 24(%r6)
add %r16, %r16, %r18
stw %r16, 24(%r6)
lis %r17, 23452
ori %r17, %r17, 51791
add %r17, %r17, %r16
add %r8, %r8, %r17
rlwinm %r17, %r14, 26, 0, 31
rlwinm %r18, %r14, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 7, 0, 31
xor %r17, %r17, %r18
add %r8, %r8, %r17
xor %r17, %r15, %r7
and %r17, %r17, %r14
xor %r17, %r17, %r7
add %r8, %r8, %r17
add %r12, %r12, %r8
rlwinm %r17, %r9, 30, 0, 31
rlwinm %r18, %r9, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r9, %r10
and %r18, %r18, %r11
and %r19, %r9, %r10
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r8, %r8, %r17
lwz %r17, 20(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 0(%r6)
add %r16, %r16, %r18
lwz %r17, 32(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 28(%r6)
add %r16, %r16, %r18
stw %r16, 28(%r6)
lis %r17, 26670
ori %r17, %r17, 28659
add %r17, %r17, %r16
add %r7, %r7, %r17
rlwinm %r17, %r12, 26, 0, 31
rlwinm %r18, %r12, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 7, 0, 31
xor %r17, %r17, %r18
add %r7, %r7, %r17
xor %r17, %r14, %r15
and %r17, %r17, %r12
xor %r17, %r17, %r15
add %r7, %r7, %r17
add %r11, %r11, %r7
rlwinm %r17, %r8, 30, 0, 31
rlwinm %r18, %r8, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r8, %r9
and %r18, %r18, %r10
and %r19, %r8, %r9
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r7, %r7, %r17
lwz %r17, 24(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 4(%r6)
add %r16, %r16, %r18
lwz %r17, 36(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 32(%r6)
add %r16, %r16, %r18
stw %r16, 32(%r6)
lis %r17, 29839
ori %r17, %r17, 33518
add %r17, %r17, %r16
add %r15, %r15, %r17
rlwinm %r17, %r11, 26, 0, 31
rlwinm %r18, %r11, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 7, 0, 31
xor %r17, %r17, %r18
add %r15, %r15, %r17
xor %r17, %r12, %r14
and %r17, %r17, %r11
xor %r17, %r17, %r14
add %r15, %r15, %r17
add %r10, %r10, %r15
rlwinm %r17, %r7, 30, 0, 31
rlwinm %r18, %r7, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r7, %r8
and %r18, %r18, %r9
and %r19, %r7, %r8
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r15, %r15, %r17
lwz %r17, 28(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 8(%r6)
add %r16, %r16, %r18
lwz %r17, 40(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 36(%r6)
add %r16, %r16, %r18
stw %r16, 36(%r6)
lis %r17, 30885
ori %r17, %r17, 25455
add %r17, %r17, %r16
add %r14, %r14, %r17
rlwinm %r17, %r10, 26, 0, 31
rlwinm %r18, %r10, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 7, 0, 31
xor %r17, %r17, %r18
add %r14, %r14, %r17
xor %r17, %r11, %r12
and %r17, %r17, %r10
xor %r17, %r17, %r12
add %r14, %r14, %r17
add %r9, %r9, %r14
rlwinm %r17, %r15, 30, 0, 31
rlwinm %r18, %r15, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r15, %r7
and %r18, %r18, %r8
and %r19, %r15, %r7
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r14, %r14, %r17
lwz %r17, 32(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 12(%r6)
add %r16, %r16, %r18
lwz %r17, 44(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 40(%r6)
add %r16, %r16, %r18
stw %r16, 40(%r6)
lis %r17, -31544
ori %r17, %r17, 30740
add %r17, %r17, %r16
add %r12, %r12, %r17
rlwinm %r17, %r9, 26, 0, 31
rlwinm %r18, %r9, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 7, 0, 31
xor %r17, %r17, %r18
add %r12, %r12, %r17
xor %r17, %r10, %r11
and %r17, %r17, %r9
xor %r17, %r17, %r11
add %r12, %r12, %r17
add %r8, %r8, %r12
rlwinm %r17, %r14, 30, 0, 31
rlwinm %r18, %r14, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r14, %r15
and %r18, %r18, %r7
and %r19, %r14, %r15
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r12, %r12, %r17
lwz %r17, 36(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 16(%r6)
add %r16, %r16, %r18
lwz %r17, 48(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 44(%r6)
add %r16, %r16, %r18
stw %r16, 44(%r6)
lis %r17, -29497
ori %r17, %r17, 520
add %r17, %r17, %r16
add %r11, %r11, %r17
rlwinm %r17, %r8, 26, 0, 31
rlwinm %r18, %r8, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 7, 0, 31
xor %r17, %r17, %r18
add %r11, %r11, %r17
xor %r17, %r9, %r10
and %r17, %r17, %r8
xor %r17, %r17, %r10
add %r11, %r11, %r17
add %r7, %r7, %r11
rlwinm %r17, %r12, 30, 0, 31
rlwinm %r18, %r12, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r12, %r14
and %r18, %r18, %r15
and %r19, %r12, %r14
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r11, %r11, %r17
lwz %r17, 40(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 20(%r6)
add %r16, %r16, %r18
lwz %r17, 52(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 48(%r6)
add %r16, %r16, %r18
stw %r16, 48(%r6)
lis %r17, -28482
ori %r17, %r17, 65530
add %r17, %r17, %r16
add %r10, %r10, %r17
rlwinm %r17, %r7, 26, 0, 31
rlwinm %r18, %r7, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r7, 7, 0, 31
xor %r17, %r17, %r18
add %r10, %r10, %r17
xor %r17, %r8, %r9
and %r17, %r17, %r7
xor %r17, %r17, %r9
add %r10, %r10, %r17
add %r15, %r15, %r10
rlwinm %r17, %r11, 30, 0, 31
rlwinm %r18, %r11, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r11, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r11, %r12
and %r18, %r18, %r14
and %r19, %r11, %r12
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r10, %r10, %r17
lwz %r17, 44(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 24(%r6)
add %r16, %r16, %r18
lwz %r17, 56(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 52(%r6)
add %r16, %r16, %r18
stw %r16, 52(%r6)
lis %r17, -23472
ori %r17, %r17, 27883
add %r17, %r17, %r16
add %r9, %r9, %r17
rlwinm %r17, %r15, 26, 0, 31
rlwinm %r18, %r15, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r15, 7, 0, 31
xor %r17, %r17, %r18
add %r9, %r9, %r17
xor %r17, %r7, %r8
and %r17, %r17, %r15
xor %r17, %r17, %r8
add %r9, %r9, %r17
add %r14, %r14, %r9
rlwinm %r17, %r10, 30, 0, 31
rlwinm %r18, %r10, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r10, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r10, %r11
and %r18, %r18, %r12
and %r19, %r10, %r11
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r9, %r9, %r17
lwz %r17, 48(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 28(%r6)
add %r16, %r16, %r18
lwz %r17, 60(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 56(%r6)
add %r16, %r16, %r18
stw %r16, 56(%r6)
lis %r17, -16647
ori %r17, %r17, 41975
add %r17, %r17, %r16
add %r8, %r8, %r17
rlwinm %r17, %r14, 26, 0, 31
rlwinm %r18, %r14, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r14, 7, 0, 31
xor %r17, %r17, %r18
add %r8, %r8, %r17
xor %r17, %r15, %r7
and %r17, %r17, %r14
xor %r17, %r17, %r7
add %r8, %r8, %r17
add %r12, %r12, %r8
rlwinm %r17, %r9, 30, 0, 31
rlwinm %r18, %r9, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r9, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r9, %r10
and %r18, %r18, %r11
and %r19, %r9, %r10
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r8, %r8, %r17
lwz %r17, 52(%r6)
rlwinm %r16, %r17, 15, 0, 31
rlwinm %r18, %r17, 13, 0, 31
xor %r16, %r16, %r18
rlwinm %r18, %r17, 22, 10, 31
xor %r16, %r16, %r18
lwz %r18, 32(%r6)
add %r16, %r16, %r18
lwz %r17, 0(%r6)
rlwinm %r18, %r17, 25, 0, 31
rlwinm %r19, %r17, 14, 0, 31
xor %r18, %r18, %r19
rlwinm %r19, %r17, 29, 3, 31
xor %r18, %r18, %r19
add %r16, %r16, %r18
lwz %r18, 60(%r6)
add %r16, %r16, %r18
stw %r16, 60(%r6)
lis %r17, -14735
ori %r17, %r17, 30962
add %r17, %r17, %r16
add %r7, %r7, %r17
rlwinm %r17, %r12, 26, 0, 31
rlwinm %r18, %r12, 21, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r12, 7, 0, 31
xor %r17, %r17, %r18
add %r7, %r7, %r17
xor %r17, %r14, %r15
and %r17, %r17, %r12
xor %r17, %r17, %r15
add %r7, %r7, %r17
add %r11, %r11, %r7
rlwinm %r17, %r8, 30, 0, 31
rlwinm %r18, %r8, 19, 0, 31
xor %r17, %r17, %r18
rlwinm %r18, %r8, 10, 0, 31
xor %r17, %r17, %r18
or %r18, %r8, %r9
and %r18, %r18, %r10
and %r19, %r8, %r9
or %r18, %r18, %r19
add %r17, %r17, %r18
add %r7, %r7, %r17
lwz %r16, 0(%r3)
lwz %r17, 4(%r3)
lwz %r18, 8(%r3)
lwz %r19, 12(%r3)
add %r7, %r7, %r16
add %r8, %r8, %r17
add %r9, %r9, %r18
add %r10, %r10, %r19
lwz %r16, 16(%r3)
lwz %r17, 20(%r3)
lwz %r18, 24(%r3)
lwz %r19, 28(%r3)
add %r11, %r11, %r16
add %r12, %r12, %r17
add %r14, %r14, %r18
add %r15, %r15, %r19
stw %r7, 0(%r3)
stw %r8, 4(%r3)
stw %r9, 8(%r3)
stw %r10, 12(%r3)
stw %r11, 16(%r3)
stw %r12, 20(%r3)
stw %r14, 24(%r3)
stw %r15, 28(%r3)
addi %r4, %r4, 64
addi %r5, %r5, -1
cmpldi %cr0, %r5, 0
bne %cr0, 22b
b 21f
20:
21:
ld %r14, 64(%r6)
ld %r15, 72(%r6)
ld %r16, 80(%r6)
ld %r17, 88(%r6)
ld %r18, 96(%r6)
ld %r19, 104(%r6)
blr
.globl sha_table_loop
.type sha_table_loop,@function
sha_table_loop:
std %r18, 8(%r6)
or %r18, %r7, %r7
std %r14, 64(%r6)
std %r15, 72(%r6)
std %r16, 80(%r6)
std %r17, 88(%r6)
std %r19, 96(%r6)
cmpldi %cr0, %r5, 0
beq %cr0, 20f
22:
lwz %r17, 0(%r3)
mtvsrd 36, %r17
lwz %r17, 4(%r3)
mtvsrd 37, %r17
lwz %r17, 8(%r3)
mtvsrd 38, %r17
lwz %r17, 12(%r3)
mtvsrd 39, %r17
lwz %r17, 16(%r3)
mtvsrd 40, %r17
lwz %r17, 20(%r3)
mtvsrd 41, %r17
lwz %r17, 24(%r3)
mtvsrd 42, %r17
lwz %r17, 28(%r3)
mtvsrd 43, %r17
lis %r16, 17034
ori %r16, %r16, 12184
mtvsrd 44, %r16
vadduwm %v11, %v11, %v12
li %r19, 8
li %r0, 0
lwbrx %r16, %r4, %r0
li %r0, 4
lwbrx %r17, %r4, %r0
mtvsrd 32, %r16
mtvsrd 44, %r17
vsldoi %v0, %v0, %v0, 8
vsldoi %v0, %v0, %v12, 8
vor %v15, %v0, %v0
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v8, 1, 5
vsel %v13, %v10, %v9, %v8
vadduwm %v10, %v10, %v14
vshasigmaw %v14, %v4, 1, 0
vadduwm %v15, %v11, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v7, %v7, %v15
vxor %v12, %v4, %v5
vsel %v12, %v5, %v6, %v12
vadduwm %v14, %v14, %v12
vadduwm %v11, %v15, %v14
vsldoi %v15, %v0, %v0, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v7, 1, 5
vsel %v13, %v9, %v8, %v7
vadduwm %v9, %v9, %v14
vshasigmaw %v14, %v11, 1, 0
vadduwm %v15, %v10, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v6, %v6, %v15
vxor %v12, %v11, %v4
vsel %v12, %v4, %v5, %v12
vadduwm %v14, %v14, %v12
vadduwm %v10, %v15, %v14
li %r0, 8
lwbrx %r16, %r4, %r0
li %r0, 12
lwbrx %r17, %r4, %r0
mtvsrd 33, %r16
mtvsrd 44, %r17
vsldoi %v1, %v1, %v1, 8
vsldoi %v1, %v1, %v12, 8
vor %v15, %v1, %v1
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v6, 1, 5
vsel %v13, %v8, %v7, %v6
vadduwm %v8, %v8, %v14
vshasigmaw %v14, %v10, 1, 0
vadduwm %v15, %v9, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v5, %v5, %v15
vxor %v12, %v10, %v11
vsel %v12, %v11, %v4, %v12
vadduwm %v14, %v14, %v12
vadduwm %v9, %v15, %v14
vsldoi %v15, %v1, %v1, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v5, 1, 5
vsel %v13, %v7, %v6, %v5
vadduwm %v7, %v7, %v14
vshasigmaw %v14, %v9, 1, 0
vadduwm %v15, %v8, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v4, %v4, %v15
vxor %v12, %v9, %v10
vsel %v12, %v10, %v11, %v12
vadduwm %v14, %v14, %v12
vadduwm %v8, %v15, %v14
li %r0, 16
lwbrx %r16, %r4, %r0
li %r0, 20
lwbrx %r17, %r4, %r0
mtvsrd 34, %r16
mtvsrd 44, %r17
vsldoi %v2, %v2, %v2, 8
vsldoi %v2, %v2, %v12, 8
vor %v15, %v2, %v2
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v4, 1, 5
vsel %v13, %v6, %v5, %v4
vadduwm %v6, %v6, %v14
vshasigmaw %v14, %v8, 1, 0
vadduwm %v15, %v7, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v11, %v11, %v15
vxor %v12, %v8, %v9
vsel %v12, %v9, %v10, %v12
vadduwm %v14, %v14, %v12
vadduwm %v7, %v15, %v14
vsldoi %v15, %v2, %v2, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v11, 1, 5
vsel %v13, %v5, %v4, %v11
vadduwm %v5, %v5, %v14
vshasigmaw %v14, %v7, 1, 0
vadduwm %v15, %v6, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v10, %v10, %v15
vxor %v12, %v7, %v8
vsel %v12, %v8, %v9, %v12
vadduwm %v14, %v14, %v12
vadduwm %v6, %v15, %v14
li %r0, 24
lwbrx %r16, %r4, %r0
li %r0, 28
lwbrx %r17, %r4, %r0
mtvsrd 35, %r16
mtvsrd 44, %r17
vsldoi %v3, %v3, %v3, 8
vsldoi %v3, %v3, %v12, 8
vor %v15, %v3, %v3
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v10, 1, 5
vsel %v13, %v4, %v11, %v10
vadduwm %v4, %v4, %v14
vshasigmaw %v14, %v6, 1, 0
vadduwm %v15, %v5, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v9, %v9, %v15
vxor %v12, %v6, %v7
vsel %v12, %v7, %v8, %v12
vadduwm %v14, %v14, %v12
vadduwm %v5, %v15, %v14
vsldoi %v15, %v3, %v3, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v9, 1, 5
vsel %v13, %v11, %v10, %v9
vadduwm %v11, %v11, %v14
vshasigmaw %v14, %v5, 1, 0
vadduwm %v15, %v4, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v8, %v8, %v15
vxor %v12, %v5, %v6
vsel %v12, %v6, %v7, %v12
vadduwm %v14, %v14, %v12
vadduwm %v4, %v15, %v14
li %r0, 32
lwbrx %r16, %r4, %r0
li %r0, 36
lwbrx %r17, %r4, %r0
mtvsrd 48, %r16
mtvsrd 44, %r17
vsldoi %v16, %v16, %v16, 8
vsldoi %v16, %v16, %v12, 8
vor %v15, %v16, %v16
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v8, 1, 5
vsel %v13, %v10, %v9, %v8
vadduwm %v10, %v10, %v14
vshasigmaw %v14, %v4, 1, 0
vadduwm %v15, %v11, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v7, %v7, %v15
vxor %v12, %v4, %v5
vsel %v12, %v5, %v6, %v12
vadduwm %v14, %v14, %v12
vadduwm %v11, %v15, %v14
vsldoi %v15, %v16, %v16, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v7, 1, 5
vsel %v13, %v9, %v8, %v7
vadduwm %v9, %v9, %v14
vshasigmaw %v14, %v11, 1, 0
vadduwm %v15, %v10, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v6, %v6, %v15
vxor %v12, %v11, %v4
vsel %v12, %v4, %v5, %v12
vadduwm %v14, %v14, %v12
vadduwm %v10, %v15, %v14
li %r0, 40
lwbrx %r16, %r4, %r0
li %r0, 44
lwbrx %r17, %r4, %r0
mtvsrd 49, %r16
mtvsrd 44, %r17
vsldoi %v17, %v17, %v17, 8
vsldoi %v17, %v17, %v12, 8
vor %v15, %v17, %v17
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v6, 1, 5
vsel %v13, %v8, %v7, %v6
vadduwm %v8, %v8, %v14
vshasigmaw %v14, %v10, 1, 0
vadduwm %v15, %v9, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v5, %v5, %v15
vxor %v12, %v10, %v11
vsel %v12, %v11, %v4, %v12
vadduwm %v14, %v14, %v12
vadduwm %v9, %v15, %v14
vsldoi %v15, %v17, %v17, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v5, 1, 5
vsel %v13, %v7, %v6, %v5
vadduwm %v7, %v7, %v14
vshasigmaw %v14, %v9, 1, 0
vadduwm %v15, %v8, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v4, %v4, %v15
vxor %v12, %v9, %v10
vsel %v12, %v10, %v11, %v12
vadduwm %v14, %v14, %v12
vadduwm %v8, %v15, %v14
li %r0, 48
lwbrx %r16, %r4, %r0
li %r0, 52
lwbrx %r17, %r4, %r0
mtvsrd 50, %r16
mtvsrd 44, %r17
vsldoi %v18, %v18, %v18, 8
vsldoi %v18, %v18, %v12, 8
vor %v15, %v18, %v18
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v4, 1, 5
vsel %v13, %v6, %v5, %v4
vadduwm %v6, %v6, %v14
vshasigmaw %v14, %v8, 1, 0
vadduwm %v15, %v7, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v11, %v11, %v15
vxor %v12, %v8, %v9
vsel %v12, %v9, %v10, %v12
vadduwm %v14, %v14, %v12
vadduwm %v7, %v15, %v14
vsldoi %v15, %v18, %v18, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v11, 1, 5
vsel %v13, %v5, %v4, %v11
vadduwm %v5, %v5, %v14
vshasigmaw %v14, %v7, 1, 0
vadduwm %v15, %v6, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v10, %v10, %v15
vxor %v12, %v7, %v8
vsel %v12, %v8, %v9, %v12
vadduwm %v14, %v14, %v12
vadduwm %v6, %v15, %v14
li %r0, 56
lwbrx %r16, %r4, %r0
li %r0, 60
lwbrx %r17, %r4, %r0
mtvsrd 51, %r16
mtvsrd 44, %r17
vsldoi %v19, %v19, %v19, 8
vsldoi %v19, %v19, %v12, 8
vor %v15, %v19, %v19
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v10, 1, 5
vsel %v13, %v4, %v11, %v10
vadduwm %v4, %v4, %v14
vshasigmaw %v14, %v6, 1, 0
vadduwm %v15, %v5, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v9, %v9, %v15
vxor %v12, %v6, %v7
vsel %v12, %v7, %v8, %v12
vadduwm %v14, %v14, %v12
vadduwm %v5, %v15, %v14
vsldoi %v15, %v19, %v19, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v9, 1, 5
vsel %v13, %v11, %v10, %v9
vadduwm %v11, %v11, %v14
vshasigmaw %v14, %v5, 1, 0
vadduwm %v15, %v4, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v8, %v8, %v15
vxor %v12, %v5, %v6
vsel %v12, %v6, %v7, %v12
vadduwm %v14, %v14, %v12
vadduwm %v4, %v15, %v14
li %r14, 3
23:
vshasigmaw %v12, %v19, 0, 5
vsldoi %v13, %v0, %v1, 8
vshasigmaw %v13, %v13, 0, 0
vsldoi %v14, %v16, %v17, 8
vadduwm %v12, %v12, %v0
vadduwm %v12, %v12, %v13
vadduwm %v0, %v12, %v14
vor %v15, %v0, %v0
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v8, 1, 5
vsel %v13, %v10, %v9, %v8
vadduwm %v10, %v10, %v14
vshasigmaw %v14, %v4, 1, 0
vadduwm %v15, %v11, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v7, %v7, %v15
vxor %v12, %v4, %v5
vsel %v12, %v5, %v6, %v12
vadduwm %v14, %v14, %v12
vadduwm %v11, %v15, %v14
vsldoi %v15, %v0, %v0, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v7, 1, 5
vsel %v13, %v9, %v8, %v7
vadduwm %v9, %v9, %v14
vshasigmaw %v14, %v11, 1, 0
vadduwm %v15, %v10, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v6, %v6, %v15
vxor %v12, %v11, %v4
vsel %v12, %v4, %v5, %v12
vadduwm %v14, %v14, %v12
vadduwm %v10, %v15, %v14
vshasigmaw %v12, %v0, 0, 5
vsldoi %v13, %v1, %v2, 8
vshasigmaw %v13, %v13, 0, 0
vsldoi %v14, %v17, %v18, 8
vadduwm %v12, %v12, %v1
vadduwm %v12, %v12, %v13
vadduwm %v1, %v12, %v14
vor %v15, %v1, %v1
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v6, 1, 5
vsel %v13, %v8, %v7, %v6
vadduwm %v8, %v8, %v14
vshasigmaw %v14, %v10, 1, 0
vadduwm %v15, %v9, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v5, %v5, %v15
vxor %v12, %v10, %v11
vsel %v12, %v11, %v4, %v12
vadduwm %v14, %v14, %v12
vadduwm %v9, %v15, %v14
vsldoi %v15, %v1, %v1, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v5, 1, 5
vsel %v13, %v7, %v6, %v5
vadduwm %v7, %v7, %v14
vshasigmaw %v14, %v9, 1, 0
vadduwm %v15, %v8, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v4, %v4, %v15
vxor %v12, %v9, %v10
vsel %v12, %v10, %v11, %v12
vadduwm %v14, %v14, %v12
vadduwm %v8, %v15, %v14
vshasigmaw %v12, %v1, 0, 5
vsldoi %v13, %v2, %v3, 8
vshasigmaw %v13, %v13, 0, 0
vsldoi %v14, %v18, %v19, 8
vadduwm %v12, %v12, %v2
vadduwm %v12, %v12, %v13
vadduwm %v2, %v12, %v14
vor %v15, %v2, %v2
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v4, 1, 5
vsel %v13, %v6, %v5, %v4
vadduwm %v6, %v6, %v14
vshasigmaw %v14, %v8, 1, 0
vadduwm %v15, %v7, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v11, %v11, %v15
vxor %v12, %v8, %v9
vsel %v12, %v9, %v10, %v12
vadduwm %v14, %v14, %v12
vadduwm %v7, %v15, %v14
vsldoi %v15, %v2, %v2, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v11, 1, 5
vsel %v13, %v5, %v4, %v11
vadduwm %v5, %v5, %v14
vshasigmaw %v14, %v7, 1, 0
vadduwm %v15, %v6, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v10, %v10, %v15
vxor %v12, %v7, %v8
vsel %v12, %v8, %v9, %v12
vadduwm %v14, %v14, %v12
vadduwm %v6, %v15, %v14
vshasigmaw %v12, %v2, 0, 5
vsldoi %v13, %v3, %v16, 8
vshasigmaw %v13, %v13, 0, 0
vsldoi %v14, %v19, %v0, 8
vadduwm %v12, %v12, %v3
vadduwm %v12, %v12, %v13
vadduwm %v3, %v12, %v14
vor %v15, %v3, %v3
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v10, 1, 5
vsel %v13, %v4, %v11, %v10
vadduwm %v4, %v4, %v14
vshasigmaw %v14, %v6, 1, 0
vadduwm %v15, %v5, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v9, %v9, %v15
vxor %v12, %v6, %v7
vsel %v12, %v7, %v8, %v12
vadduwm %v14, %v14, %v12
vadduwm %v5, %v15, %v14
vsldoi %v15, %v3, %v3, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v9, 1, 5
vsel %v13, %v11, %v10, %v9
vadduwm %v11, %v11, %v14
vshasigmaw %v14, %v5, 1, 0
vadduwm %v15, %v4, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v8, %v8, %v15
vxor %v12, %v5, %v6
vsel %v12, %v6, %v7, %v12
vadduwm %v14, %v14, %v12
vadduwm %v4, %v15, %v14
vshasigmaw %v12, %v3, 0, 5
vsldoi %v13, %v16, %v17, 8
vshasigmaw %v13, %v13, 0, 0
vsldoi %v14, %v0, %v1, 8
vadduwm %v12, %v12, %v16
vadduwm %v12, %v12, %v13
vadduwm %v16, %v12, %v14
vor %v15, %v16, %v16
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v8, 1, 5
vsel %v13, %v10, %v9, %v8
vadduwm %v10, %v10, %v14
vshasigmaw %v14, %v4, 1, 0
vadduwm %v15, %v11, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v7, %v7, %v15
vxor %v12, %v4, %v5
vsel %v12, %v5, %v6, %v12
vadduwm %v14, %v14, %v12
vadduwm %v11, %v15, %v14
vsldoi %v15, %v16, %v16, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v7, 1, 5
vsel %v13, %v9, %v8, %v7
vadduwm %v9, %v9, %v14
vshasigmaw %v14, %v11, 1, 0
vadduwm %v15, %v10, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v6, %v6, %v15
vxor %v12, %v11, %v4
vsel %v12, %v4, %v5, %v12
vadduwm %v14, %v14, %v12
vadduwm %v10, %v15, %v14
vshasigmaw %v12, %v16, 0, 5
vsldoi %v13, %v17, %v18, 8
vshasigmaw %v13, %v13, 0, 0
vsldoi %v14, %v1, %v2, 8
vadduwm %v12, %v12, %v17
vadduwm %v12, %v12, %v13
vadduwm %v17, %v12, %v14
vor %v15, %v17, %v17
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v6, 1, 5
vsel %v13, %v8, %v7, %v6
vadduwm %v8, %v8, %v14
vshasigmaw %v14, %v10, 1, 0
vadduwm %v15, %v9, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v5, %v5, %v15
vxor %v12, %v10, %v11
vsel %v12, %v11, %v4, %v12
vadduwm %v14, %v14, %v12
vadduwm %v9, %v15, %v14
vsldoi %v15, %v17, %v17, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v5, 1, 5
vsel %v13, %v7, %v6, %v5
vadduwm %v7, %v7, %v14
vshasigmaw %v14, %v9, 1, 0
vadduwm %v15, %v8, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v4, %v4, %v15
vxor %v12, %v9, %v10
vsel %v12, %v10, %v11, %v12
vadduwm %v14, %v14, %v12
vadduwm %v8, %v15, %v14
vshasigmaw %v12, %v17, 0, 5
vsldoi %v13, %v18, %v19, 8
vshasigmaw %v13, %v13, 0, 0
vsldoi %v14, %v2, %v3, 8
vadduwm %v12, %v12, %v18
vadduwm %v12, %v12, %v13
vadduwm %v18, %v12, %v14
vor %v15, %v18, %v18
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v4, 1, 5
vsel %v13, %v6, %v5, %v4
vadduwm %v6, %v6, %v14
vshasigmaw %v14, %v8, 1, 0
vadduwm %v15, %v7, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v11, %v11, %v15
vxor %v12, %v8, %v9
vsel %v12, %v9, %v10, %v12
vadduwm %v14, %v14, %v12
vadduwm %v7, %v15, %v14
vsldoi %v15, %v18, %v18, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v11, 1, 5
vsel %v13, %v5, %v4, %v11
vadduwm %v5, %v5, %v14
vshasigmaw %v14, %v7, 1, 0
vadduwm %v15, %v6, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v10, %v10, %v15
vxor %v12, %v7, %v8
vsel %v12, %v8, %v9, %v12
vadduwm %v14, %v14, %v12
vadduwm %v6, %v15, %v14
vshasigmaw %v12, %v18, 0, 5
vsldoi %v13, %v19, %v0, 8
vshasigmaw %v13, %v13, 0, 0
vsldoi %v14, %v3, %v16, 8
vadduwm %v12, %v12, %v19
vadduwm %v12, %v12, %v13
vadduwm %v19, %v12, %v14
vor %v15, %v19, %v19
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v10, 1, 5
vsel %v13, %v4, %v11, %v10
vadduwm %v4, %v4, %v14
vshasigmaw %v14, %v6, 1, 0
vadduwm %v15, %v5, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v9, %v9, %v15
vxor %v12, %v6, %v7
vsel %v12, %v7, %v8, %v12
vadduwm %v14, %v14, %v12
vadduwm %v5, %v15, %v14
vsldoi %v15, %v19, %v19, 8
lxvd2x 46, %r18, %r19
addi %r19, %r19, 8
vshasigmaw %v12, %v9, 1, 5
vsel %v13, %v11, %v10, %v9
vadduwm %v11, %v11, %v14
vshasigmaw %v14, %v5, 1, 0
vadduwm %v15, %v4, %v15
vadduwm %v15, %v15, %v13
vadduwm %v15, %v15, %v12
vadduwm %v8, %v8, %v15
vxor %v12, %v5, %v6
vsel %v12, %v6, %v7, %v12
vadduwm %v14, %v14, %v12
vadduwm %v4, %v15, %v14
addi %r14, %r14, -1
cmpldi %cr0, %r14, 0
bne %cr0, 23b
mfvsrd %r7, 36
mfvsrd %r8, 37
mfvsrd %r9, 38
mfvsrd %r10, 39
mfvsrd %r11, 40
mfvsrd %r12, 41
mfvsrd %r14, 42
mfvsrd %r15, 43
lwz %r16, 0(%r3)
lwz %r17, 4(%r3)
lwz %r0, 8(%r3)
lwz %r19, 12(%r3)
add %r7, %r7, %r16
add %r8, %r8, %r17
add %r9, %r9, %r0
add %r10, %r10, %r19
lwz %r16, 16(%r3)
lwz %r17, 20(%r3)
lwz %r0, 24(%r3)
lwz %r19, 28(%r3)
add %r11, %r11, %r16
add %r12, %r12, %r17
add %r14, %r14, %r0
add %r15, %r15, %r19
stw %r7, 0(%r3)
stw %r8, 4(%r3)
stw %r9, 8(%r3)
stw %r10, 12(%r3)
stw %r11, 16(%r3)
stw %r12, 20(%r3)
stw %r14, 24(%r3)
stw %r15, 28(%r3)
addi %r4, %r4, 64
addi %r5, %r5, -1
cmpldi %cr0, %r5, 0
bne %cr0, 22b
b 21f
20:
21:
ld %r14, 64(%r6)
ld %r15, 72(%r6)
ld %r16, 80(%r6)
ld %r17, 88(%r6)
ld %r19, 96(%r6)
ld %r18, 8(%r6)
blr
