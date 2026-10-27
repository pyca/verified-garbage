.text
.p2align 6
.globl trial_scalar
trial_scalar:
ldr w2, [x0, #0]
ldr w3, [x0, #4]
ldr w4, [x0, #8]
ldr w5, [x0, #12]
ldr w6, [x0, #16]
ldr w7, [x0, #20]
ldr w8, [x0, #24]
ldr w9, [x0, #28]
ldr w10, [x0, #32]
ldr w11, [x0, #36]
ldr w12, [x0, #40]
ldr w13, [x0, #44]
ldr w14, [x0, #48]
ldr w15, [x0, #52]
ldr w16, [x0, #56]
ldr w17, [x0, #60]
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
ldr w1, [x0, #0]
add w2, w2, w1
str w2, [x0, #0]
ldr w1, [x0, #4]
add w3, w3, w1
str w3, [x0, #4]
ldr w1, [x0, #8]
add w4, w4, w1
str w4, [x0, #8]
ldr w1, [x0, #12]
add w5, w5, w1
str w5, [x0, #12]
ldr w1, [x0, #16]
add w6, w6, w1
str w6, [x0, #16]
ldr w1, [x0, #20]
add w7, w7, w1
str w7, [x0, #20]
ldr w1, [x0, #24]
add w8, w8, w1
str w8, [x0, #24]
ldr w1, [x0, #28]
add w9, w9, w1
str w9, [x0, #28]
ldr w1, [x0, #32]
add w10, w10, w1
str w10, [x0, #32]
ldr w1, [x0, #36]
add w11, w11, w1
str w11, [x0, #36]
ldr w1, [x0, #40]
add w12, w12, w1
str w12, [x0, #40]
ldr w1, [x0, #44]
add w13, w13, w1
str w13, [x0, #44]
ldr w1, [x0, #48]
add w14, w14, w1
str w14, [x0, #48]
ldr w1, [x0, #52]
add w15, w15, w1
str w15, [x0, #52]
ldr w1, [x0, #56]
add w16, w16, w1
str w16, [x0, #56]
ldr w1, [x0, #60]
add w17, w17, w1
str w17, [x0, #60]
ret
.p2align 6
.globl trial_neon
trial_neon:
ldr q0, [x0, #0]
ldr q1, [x0, #16]
ldr q2, [x0, #32]
ldr q3, [x0, #48]
mov v4.16b, v0.16b
mov v5.16b, v1.16b
mov v6.16b, v2.16b
mov v7.16b, v3.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
zip1 v16.4s, v0.4s, v1.4s
zip2 v17.4s, v0.4s, v1.4s
zip1 v18.4s, v2.4s, v3.4s
zip2 v19.4s, v2.4s, v3.4s
zip1 v0.2d, v16.2d, v18.2d
zip2 v1.2d, v16.2d, v18.2d
zip1 v2.2d, v17.2d, v19.2d
zip2 v3.2d, v17.2d, v19.2d
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
zip1 v16.4s, v0.4s, v1.4s
zip2 v17.4s, v0.4s, v1.4s
zip1 v18.4s, v2.4s, v3.4s
zip2 v19.4s, v2.4s, v3.4s
zip1 v0.2d, v16.2d, v18.2d
zip2 v1.2d, v16.2d, v18.2d
zip1 v2.2d, v17.2d, v19.2d
zip2 v3.2d, v17.2d, v19.2d
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v0.4s, v0.4s, v4.4s
add v1.4s, v1.4s, v5.4s
add v2.4s, v2.4s, v6.4s
add v3.4s, v3.4s, v7.4s
str q0, [x0, #0]
str q1, [x0, #16]
str q2, [x0, #32]
str q3, [x0, #48]
ret
.p2align 6
.globl trial_neon_loop
trial_neon_loop:
ldr q0, [x0, #0]
ldr q1, [x0, #16]
ldr q2, [x0, #32]
ldr q3, [x0, #48]
mov v4.16b, v0.16b
mov v5.16b, v1.16b
mov v6.16b, v2.16b
mov v7.16b, v3.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
zip1 v16.4s, v0.4s, v1.4s
zip2 v17.4s, v0.4s, v1.4s
zip1 v18.4s, v2.4s, v3.4s
zip2 v19.4s, v2.4s, v3.4s
zip1 v0.2d, v16.2d, v18.2d
zip2 v1.2d, v16.2d, v18.2d
zip1 v2.2d, v17.2d, v19.2d
zip2 v3.2d, v17.2d, v19.2d
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
movz x2, #4, lsl #0
20:
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
sub x2, x2, #1
cbnz x2, 20b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
zip1 v16.4s, v0.4s, v1.4s
zip2 v17.4s, v0.4s, v1.4s
zip1 v18.4s, v2.4s, v3.4s
zip2 v19.4s, v2.4s, v3.4s
zip1 v0.2d, v16.2d, v18.2d
zip2 v1.2d, v16.2d, v18.2d
zip1 v2.2d, v17.2d, v19.2d
zip2 v3.2d, v17.2d, v19.2d
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v0.4s, v0.4s, v4.4s
add v1.4s, v1.4s, v5.4s
add v2.4s, v2.4s, v6.4s
add v3.4s, v3.4s, v7.4s
str q0, [x0, #0]
str q1, [x0, #16]
str q2, [x0, #32]
str q3, [x0, #48]
ret
.p2align 6
.globl trial_fold
trial_fold:
ldr w2, [x0, #0]
ldr w3, [x0, #4]
ldr w4, [x0, #8]
ldr w5, [x0, #12]
ldr w6, [x0, #16]
ldr w7, [x0, #20]
ldr w8, [x0, #24]
ldr w9, [x0, #28]
ldr w10, [x0, #32]
ldr w11, [x0, #36]
ldr w12, [x0, #40]
ldr w13, [x0, #44]
ldr w14, [x0, #48]
ldr w15, [x0, #52]
ldr w16, [x0, #56]
ldr w17, [x0, #60]
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
ldr w1, [x0, #0]
add w2, w2, w1
str w2, [x0, #0]
ldr w1, [x0, #4]
add w3, w3, w1
str w3, [x0, #4]
ldr w1, [x0, #8]
add w4, w4, w1
str w4, [x0, #8]
ldr w1, [x0, #12]
add w5, w5, w1
str w5, [x0, #12]
ldr w1, [x0, #16]
add w6, w6, w1
str w6, [x0, #16]
ldr w1, [x0, #20]
add w7, w7, w1
str w7, [x0, #20]
ldr w1, [x0, #24]
add w8, w8, w1
str w8, [x0, #24]
ldr w1, [x0, #28]
add w9, w9, w1
str w9, [x0, #28]
ldr w1, [x0, #32]
add w10, w10, w1
str w10, [x0, #32]
ldr w1, [x0, #36]
add w11, w11, w1
str w11, [x0, #36]
ldr w1, [x0, #40]
add w12, w12, w1
str w12, [x0, #40]
ldr w1, [x0, #44]
add w13, w13, w1
str w13, [x0, #44]
ldr w1, [x0, #48]
add w14, w14, w1
str w14, [x0, #48]
ldr w1, [x0, #52]
add w15, w15, w1
str w15, [x0, #52]
ldr w1, [x0, #56]
add w16, w16, w1
str w16, [x0, #56]
ldr w1, [x0, #60]
add w17, w17, w1
str w17, [x0, #60]
ret
.p2align 6
.globl trial_fold_io
trial_fold_io:
ldr q4, [x0, #0]
ldr q5, [x0, #16]
ldr q6, [x0, #32]
ldr q7, [x0, #48]
umov x2, v4.d[0]
lsr x3, x2, #32
umov x4, v4.d[1]
lsr x5, x4, #32
umov x6, v5.d[0]
lsr x7, x6, #32
umov x8, v5.d[1]
lsr x9, x8, #32
umov x10, v6.d[0]
lsr x11, x10, #32
umov x12, v6.d[1]
lsr x13, x12, #32
umov x14, v7.d[0]
lsr x15, x14, #32
umov x16, v7.d[1]
lsr x17, x16, #32
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
lsl x1, x3, #32
orr x1, x1, x2
mov v0.d[0], x1
lsl x1, x5, #32
orr x1, x1, x4
mov v0.d[1], x1
lsl x1, x7, #32
orr x1, x1, x6
mov v1.d[0], x1
lsl x1, x9, #32
orr x1, x1, x8
mov v1.d[1], x1
lsl x1, x11, #32
orr x1, x1, x10
mov v2.d[0], x1
lsl x1, x13, #32
orr x1, x1, x12
mov v2.d[1], x1
lsl x1, x15, #32
orr x1, x1, x14
mov v3.d[0], x1
lsl x1, x17, #32
orr x1, x1, x16
mov v3.d[1], x1
add v0.4s, v0.4s, v4.4s
add v1.4s, v1.4s, v5.4s
add v2.4s, v2.4s, v6.4s
add v3.4s, v3.4s, v7.4s
str q0, [x0, #0]
str q1, [x0, #16]
str q2, [x0, #32]
str q3, [x0, #48]
ret
.p2align 6
.globl trial_schedule
trial_schedule:
ldr w2, [x0, #0]
ldr w3, [x0, #4]
ldr w4, [x0, #8]
ldr w5, [x0, #12]
ldr w6, [x0, #16]
ldr w7, [x0, #20]
ldr w8, [x0, #24]
ldr w9, [x0, #28]
ldr w10, [x0, #32]
ldr w11, [x0, #36]
ldr w12, [x0, #40]
ldr w13, [x0, #44]
ldr w14, [x0, #48]
ldr w15, [x0, #52]
ldr w16, [x0, #56]
ldr w17, [x0, #60]
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
ldr w1, [x0, #0]
add w2, w2, w1
str w2, [x0, #0]
ldr w1, [x0, #4]
add w3, w3, w1
str w3, [x0, #4]
ldr w1, [x0, #8]
add w4, w4, w1
str w4, [x0, #8]
ldr w1, [x0, #12]
add w5, w5, w1
str w5, [x0, #12]
ldr w1, [x0, #16]
add w6, w6, w1
str w6, [x0, #16]
ldr w1, [x0, #20]
add w7, w7, w1
str w7, [x0, #20]
ldr w1, [x0, #24]
add w8, w8, w1
str w8, [x0, #24]
ldr w1, [x0, #28]
add w9, w9, w1
str w9, [x0, #28]
ldr w1, [x0, #32]
add w10, w10, w1
str w10, [x0, #32]
ldr w1, [x0, #36]
add w11, w11, w1
str w11, [x0, #36]
ldr w1, [x0, #40]
add w12, w12, w1
str w12, [x0, #40]
ldr w1, [x0, #44]
add w13, w13, w1
str w13, [x0, #44]
ldr w1, [x0, #48]
add w14, w14, w1
str w14, [x0, #48]
ldr w1, [x0, #52]
add w15, w15, w1
str w15, [x0, #52]
ldr w1, [x0, #56]
add w16, w16, w1
str w16, [x0, #56]
ldr w1, [x0, #60]
add w17, w17, w1
str w17, [x0, #60]
ret
.p2align 6
.globl trial_schedule_fold
trial_schedule_fold:
ldr w2, [x0, #0]
ldr w3, [x0, #4]
ldr w4, [x0, #8]
ldr w5, [x0, #12]
ldr w6, [x0, #16]
ldr w7, [x0, #20]
ldr w8, [x0, #24]
ldr w9, [x0, #28]
ldr w10, [x0, #32]
ldr w11, [x0, #36]
ldr w12, [x0, #40]
ldr w13, [x0, #44]
ldr w14, [x0, #48]
ldr w15, [x0, #52]
ldr w16, [x0, #56]
ldr w17, [x0, #60]
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w16, w15
eor w17, w17, w1, ror #14
ldr w1, [x0, #0]
add w2, w2, w1
str w2, [x0, #0]
ldr w1, [x0, #4]
add w3, w3, w1
str w3, [x0, #4]
ldr w1, [x0, #8]
add w4, w4, w1
str w4, [x0, #8]
ldr w1, [x0, #12]
add w5, w5, w1
str w5, [x0, #12]
ldr w1, [x0, #16]
add w6, w6, w1
str w6, [x0, #16]
ldr w1, [x0, #20]
add w7, w7, w1
str w7, [x0, #20]
ldr w1, [x0, #24]
add w8, w8, w1
str w8, [x0, #24]
ldr w1, [x0, #28]
add w9, w9, w1
str w9, [x0, #28]
ldr w1, [x0, #32]
add w10, w10, w1
str w10, [x0, #32]
ldr w1, [x0, #36]
add w11, w11, w1
str w11, [x0, #36]
ldr w1, [x0, #40]
add w12, w12, w1
str w12, [x0, #40]
ldr w1, [x0, #44]
add w13, w13, w1
str w13, [x0, #44]
ldr w1, [x0, #48]
add w14, w14, w1
str w14, [x0, #48]
ldr w1, [x0, #52]
add w15, w15, w1
str w15, [x0, #52]
ldr w1, [x0, #56]
add w16, w16, w1
str w16, [x0, #56]
ldr w1, [x0, #60]
add w17, w17, w1
str w17, [x0, #60]
ret
.p2align 6
.globl trial_bm_scalar
trial_bm_scalar:
str x30, [sp, #-16]!
str x19, [x4, #64]
str x20, [x4, #72]
str x21, [x4, #80]
str x23, [x4, #88]
str x24, [x4, #96]
str x22, [x4, #104]
add x23, x1, #0
add x19, x0, #0
add x20, x2, #0
add x22, x4, #0
lsl x9, x1, #6
add x21, x2, x9
lsl x9, x1, #7
add x24, x0, x9
sub x24, x24, #64
20:
ldr x9, [x24, #0]
ldr x10, [x19, #0]
eor x9, x9, x10
str x9, [x20, #0]
ldr x9, [x24, #8]
ldr x10, [x19, #8]
eor x9, x9, x10
str x9, [x20, #8]
ldr x9, [x24, #16]
ldr x10, [x19, #16]
eor x9, x9, x10
str x9, [x20, #16]
ldr x9, [x24, #24]
ldr x10, [x19, #24]
eor x9, x9, x10
str x9, [x20, #24]
ldr x9, [x24, #32]
ldr x10, [x19, #32]
eor x9, x9, x10
str x9, [x20, #32]
ldr x9, [x24, #40]
ldr x10, [x19, #40]
eor x9, x9, x10
str x9, [x20, #40]
ldr x9, [x24, #48]
ldr x10, [x19, #48]
eor x9, x9, x10
str x9, [x20, #48]
ldr x9, [x24, #56]
ldr x10, [x19, #56]
eor x9, x9, x10
str x9, [x20, #56]
add x0, x20, #0
add x1, x22, #0
bl trial_scalar
add x19, x19, #64
ldr x9, [x20, #0]
ldr x10, [x19, #0]
eor x9, x9, x10
str x9, [x21, #0]
ldr x9, [x20, #8]
ldr x10, [x19, #8]
eor x9, x9, x10
str x9, [x21, #8]
ldr x9, [x20, #16]
ldr x10, [x19, #16]
eor x9, x9, x10
str x9, [x21, #16]
ldr x9, [x20, #24]
ldr x10, [x19, #24]
eor x9, x9, x10
str x9, [x21, #24]
ldr x9, [x20, #32]
ldr x10, [x19, #32]
eor x9, x9, x10
str x9, [x21, #32]
ldr x9, [x20, #40]
ldr x10, [x19, #40]
eor x9, x9, x10
str x9, [x21, #40]
ldr x9, [x20, #48]
ldr x10, [x19, #48]
eor x9, x9, x10
str x9, [x21, #48]
ldr x9, [x20, #56]
ldr x10, [x19, #56]
eor x9, x9, x10
str x9, [x21, #56]
add x0, x21, #0
add x1, x22, #0
bl trial_scalar
add x24, x21, #0
add x19, x19, #64
add x20, x20, #64
add x21, x21, #64
sub x23, x23, #1
cbnz x23, 20b
ldr x19, [x22, #64]
ldr x20, [x22, #72]
ldr x21, [x22, #80]
ldr x23, [x22, #88]
ldr x24, [x22, #96]
ldr x22, [x22, #104]
ldr x30, [sp], #16
ret
.p2align 6
.globl trial_bm_neon
trial_bm_neon:
str x30, [sp, #-16]!
str x19, [x4, #64]
str x20, [x4, #72]
str x21, [x4, #80]
str x23, [x4, #88]
str x24, [x4, #96]
str x22, [x4, #104]
add x23, x1, #0
add x19, x0, #0
add x20, x2, #0
add x22, x4, #0
lsl x9, x1, #6
add x21, x2, x9
lsl x9, x1, #7
add x24, x0, x9
sub x24, x24, #64
20:
ldr x9, [x24, #0]
ldr x10, [x19, #0]
eor x9, x9, x10
str x9, [x20, #0]
ldr x9, [x24, #8]
ldr x10, [x19, #8]
eor x9, x9, x10
str x9, [x20, #8]
ldr x9, [x24, #16]
ldr x10, [x19, #16]
eor x9, x9, x10
str x9, [x20, #16]
ldr x9, [x24, #24]
ldr x10, [x19, #24]
eor x9, x9, x10
str x9, [x20, #24]
ldr x9, [x24, #32]
ldr x10, [x19, #32]
eor x9, x9, x10
str x9, [x20, #32]
ldr x9, [x24, #40]
ldr x10, [x19, #40]
eor x9, x9, x10
str x9, [x20, #40]
ldr x9, [x24, #48]
ldr x10, [x19, #48]
eor x9, x9, x10
str x9, [x20, #48]
ldr x9, [x24, #56]
ldr x10, [x19, #56]
eor x9, x9, x10
str x9, [x20, #56]
add x0, x20, #0
add x1, x22, #0
bl trial_neon
add x19, x19, #64
ldr x9, [x20, #0]
ldr x10, [x19, #0]
eor x9, x9, x10
str x9, [x21, #0]
ldr x9, [x20, #8]
ldr x10, [x19, #8]
eor x9, x9, x10
str x9, [x21, #8]
ldr x9, [x20, #16]
ldr x10, [x19, #16]
eor x9, x9, x10
str x9, [x21, #16]
ldr x9, [x20, #24]
ldr x10, [x19, #24]
eor x9, x9, x10
str x9, [x21, #24]
ldr x9, [x20, #32]
ldr x10, [x19, #32]
eor x9, x9, x10
str x9, [x21, #32]
ldr x9, [x20, #40]
ldr x10, [x19, #40]
eor x9, x9, x10
str x9, [x21, #40]
ldr x9, [x20, #48]
ldr x10, [x19, #48]
eor x9, x9, x10
str x9, [x21, #48]
ldr x9, [x20, #56]
ldr x10, [x19, #56]
eor x9, x9, x10
str x9, [x21, #56]
add x0, x21, #0
add x1, x22, #0
bl trial_neon
add x24, x21, #0
add x19, x19, #64
add x20, x20, #64
add x21, x21, #64
sub x23, x23, #1
cbnz x23, 20b
ldr x19, [x22, #64]
ldr x20, [x22, #72]
ldr x21, [x22, #80]
ldr x23, [x22, #88]
ldr x24, [x22, #96]
ldr x22, [x22, #104]
ldr x30, [sp], #16
ret
.p2align 6
.globl trial_bm_neon_loop
trial_bm_neon_loop:
str x30, [sp, #-16]!
str x19, [x4, #64]
str x20, [x4, #72]
str x21, [x4, #80]
str x23, [x4, #88]
str x24, [x4, #96]
str x22, [x4, #104]
add x23, x1, #0
add x19, x0, #0
add x20, x2, #0
add x22, x4, #0
lsl x9, x1, #6
add x21, x2, x9
lsl x9, x1, #7
add x24, x0, x9
sub x24, x24, #64
20:
ldr x9, [x24, #0]
ldr x10, [x19, #0]
eor x9, x9, x10
str x9, [x20, #0]
ldr x9, [x24, #8]
ldr x10, [x19, #8]
eor x9, x9, x10
str x9, [x20, #8]
ldr x9, [x24, #16]
ldr x10, [x19, #16]
eor x9, x9, x10
str x9, [x20, #16]
ldr x9, [x24, #24]
ldr x10, [x19, #24]
eor x9, x9, x10
str x9, [x20, #24]
ldr x9, [x24, #32]
ldr x10, [x19, #32]
eor x9, x9, x10
str x9, [x20, #32]
ldr x9, [x24, #40]
ldr x10, [x19, #40]
eor x9, x9, x10
str x9, [x20, #40]
ldr x9, [x24, #48]
ldr x10, [x19, #48]
eor x9, x9, x10
str x9, [x20, #48]
ldr x9, [x24, #56]
ldr x10, [x19, #56]
eor x9, x9, x10
str x9, [x20, #56]
add x0, x20, #0
add x1, x22, #0
bl trial_neon_loop
add x19, x19, #64
ldr x9, [x20, #0]
ldr x10, [x19, #0]
eor x9, x9, x10
str x9, [x21, #0]
ldr x9, [x20, #8]
ldr x10, [x19, #8]
eor x9, x9, x10
str x9, [x21, #8]
ldr x9, [x20, #16]
ldr x10, [x19, #16]
eor x9, x9, x10
str x9, [x21, #16]
ldr x9, [x20, #24]
ldr x10, [x19, #24]
eor x9, x9, x10
str x9, [x21, #24]
ldr x9, [x20, #32]
ldr x10, [x19, #32]
eor x9, x9, x10
str x9, [x21, #32]
ldr x9, [x20, #40]
ldr x10, [x19, #40]
eor x9, x9, x10
str x9, [x21, #40]
ldr x9, [x20, #48]
ldr x10, [x19, #48]
eor x9, x9, x10
str x9, [x21, #48]
ldr x9, [x20, #56]
ldr x10, [x19, #56]
eor x9, x9, x10
str x9, [x21, #56]
add x0, x21, #0
add x1, x22, #0
bl trial_neon_loop
add x24, x21, #0
add x19, x19, #64
add x20, x20, #64
add x21, x21, #64
sub x23, x23, #1
cbnz x23, 20b
ldr x19, [x22, #64]
ldr x20, [x22, #72]
ldr x21, [x22, #80]
ldr x23, [x22, #88]
ldr x24, [x22, #96]
ldr x22, [x22, #104]
ldr x30, [sp], #16
ret
.p2align 6
.globl trial_bm_fused
trial_bm_fused:
lsl x5, x1, #6
add x6, x2, x5
lsl x5, x1, #7
add x5, x0, x5
sub x5, x5, #64
ldr q0, [x5, #0]
ldr q1, [x5, #16]
ldr q2, [x5, #32]
ldr q3, [x5, #48]
20:
ldr q16, [x0, #0]
ldr q17, [x0, #16]
ldr q18, [x0, #32]
ldr q19, [x0, #48]
eor v0.16b, v0.16b, v16.16b
eor v1.16b, v1.16b, v17.16b
eor v2.16b, v2.16b, v18.16b
eor v3.16b, v3.16b, v19.16b
mov v4.16b, v0.16b
mov v5.16b, v1.16b
mov v6.16b, v2.16b
mov v7.16b, v3.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
zip1 v16.4s, v0.4s, v1.4s
zip2 v17.4s, v0.4s, v1.4s
zip1 v18.4s, v2.4s, v3.4s
zip2 v19.4s, v2.4s, v3.4s
zip1 v0.2d, v16.2d, v18.2d
zip2 v1.2d, v16.2d, v18.2d
zip1 v2.2d, v17.2d, v19.2d
zip2 v3.2d, v17.2d, v19.2d
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
zip1 v16.4s, v0.4s, v1.4s
zip2 v17.4s, v0.4s, v1.4s
zip1 v18.4s, v2.4s, v3.4s
zip2 v19.4s, v2.4s, v3.4s
zip1 v0.2d, v16.2d, v18.2d
zip2 v1.2d, v16.2d, v18.2d
zip1 v2.2d, v17.2d, v19.2d
zip2 v3.2d, v17.2d, v19.2d
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v0.4s, v0.4s, v4.4s
add v1.4s, v1.4s, v5.4s
add v2.4s, v2.4s, v6.4s
add v3.4s, v3.4s, v7.4s
str q0, [x2, #0]
str q1, [x2, #16]
str q2, [x2, #32]
str q3, [x2, #48]
add x0, x0, #64
ldr q16, [x0, #0]
ldr q17, [x0, #16]
ldr q18, [x0, #32]
ldr q19, [x0, #48]
eor v0.16b, v0.16b, v16.16b
eor v1.16b, v1.16b, v17.16b
eor v2.16b, v2.16b, v18.16b
eor v3.16b, v3.16b, v19.16b
mov v4.16b, v0.16b
mov v5.16b, v1.16b
mov v6.16b, v2.16b
mov v7.16b, v3.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
zip1 v16.4s, v0.4s, v1.4s
zip2 v17.4s, v0.4s, v1.4s
zip1 v18.4s, v2.4s, v3.4s
zip2 v19.4s, v2.4s, v3.4s
zip1 v0.2d, v16.2d, v18.2d
zip2 v1.2d, v16.2d, v18.2d
zip1 v2.2d, v17.2d, v19.2d
zip2 v3.2d, v17.2d, v19.2d
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
zip1 v16.4s, v0.4s, v1.4s
zip2 v17.4s, v0.4s, v1.4s
zip1 v18.4s, v2.4s, v3.4s
zip2 v19.4s, v2.4s, v3.4s
zip1 v0.2d, v16.2d, v18.2d
zip2 v1.2d, v16.2d, v18.2d
zip1 v2.2d, v17.2d, v19.2d
zip2 v3.2d, v17.2d, v19.2d
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v0.4s, v0.4s, v4.4s
add v1.4s, v1.4s, v5.4s
add v2.4s, v2.4s, v6.4s
add v3.4s, v3.4s, v7.4s
str q0, [x6, #0]
str q1, [x6, #16]
str q2, [x6, #32]
str q3, [x6, #48]
add x0, x0, #64
add x2, x2, #64
add x6, x6, #64
sub x1, x1, #1
cbnz x1, 20b
ret
.p2align 6
.globl trial_bm_fused_loop
trial_bm_fused_loop:
lsl x5, x1, #6
add x6, x2, x5
lsl x5, x1, #7
add x5, x0, x5
sub x5, x5, #64
ldr q0, [x5, #0]
ldr q1, [x5, #16]
ldr q2, [x5, #32]
ldr q3, [x5, #48]
20:
ldr q16, [x0, #0]
ldr q17, [x0, #16]
ldr q18, [x0, #32]
ldr q19, [x0, #48]
eor v0.16b, v0.16b, v16.16b
eor v1.16b, v1.16b, v17.16b
eor v2.16b, v2.16b, v18.16b
eor v3.16b, v3.16b, v19.16b
mov v4.16b, v0.16b
mov v5.16b, v1.16b
mov v6.16b, v2.16b
mov v7.16b, v3.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
zip1 v16.4s, v0.4s, v1.4s
zip2 v17.4s, v0.4s, v1.4s
zip1 v18.4s, v2.4s, v3.4s
zip2 v19.4s, v2.4s, v3.4s
zip1 v0.2d, v16.2d, v18.2d
zip2 v1.2d, v16.2d, v18.2d
zip1 v2.2d, v17.2d, v19.2d
zip2 v3.2d, v17.2d, v19.2d
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
movz x7, #4, lsl #0
21:
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
sub x7, x7, #1
cbnz x7, 21b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
zip1 v16.4s, v0.4s, v1.4s
zip2 v17.4s, v0.4s, v1.4s
zip1 v18.4s, v2.4s, v3.4s
zip2 v19.4s, v2.4s, v3.4s
zip1 v0.2d, v16.2d, v18.2d
zip2 v1.2d, v16.2d, v18.2d
zip1 v2.2d, v17.2d, v19.2d
zip2 v3.2d, v17.2d, v19.2d
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v0.4s, v0.4s, v4.4s
add v1.4s, v1.4s, v5.4s
add v2.4s, v2.4s, v6.4s
add v3.4s, v3.4s, v7.4s
str q0, [x2, #0]
str q1, [x2, #16]
str q2, [x2, #32]
str q3, [x2, #48]
add x0, x0, #64
ldr q16, [x0, #0]
ldr q17, [x0, #16]
ldr q18, [x0, #32]
ldr q19, [x0, #48]
eor v0.16b, v0.16b, v16.16b
eor v1.16b, v1.16b, v17.16b
eor v2.16b, v2.16b, v18.16b
eor v3.16b, v3.16b, v19.16b
mov v4.16b, v0.16b
mov v5.16b, v1.16b
mov v6.16b, v2.16b
mov v7.16b, v3.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
zip1 v16.4s, v0.4s, v1.4s
zip2 v17.4s, v0.4s, v1.4s
zip1 v18.4s, v2.4s, v3.4s
zip2 v19.4s, v2.4s, v3.4s
zip1 v0.2d, v16.2d, v18.2d
zip2 v1.2d, v16.2d, v18.2d
zip1 v2.2d, v17.2d, v19.2d
zip2 v3.2d, v17.2d, v19.2d
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
movz x7, #4, lsl #0
22:
add v20.4s, v0.4s, v1.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v3.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
add v20.4s, v0.4s, v3.4s
ushr v21.4s, v20.4s, #25
sli v21.4s, v20.4s, #7
eor v1.16b, v1.16b, v21.16b
add v20.4s, v1.4s, v0.4s
ushr v21.4s, v20.4s, #23
sli v21.4s, v20.4s, #9
eor v2.16b, v2.16b, v21.16b
add v20.4s, v2.4s, v1.4s
ushr v21.4s, v20.4s, #19
sli v21.4s, v20.4s, #13
eor v3.16b, v3.16b, v21.16b
add v20.4s, v3.4s, v2.4s
ushr v21.4s, v20.4s, #14
sli v21.4s, v20.4s, #18
eor v0.16b, v0.16b, v21.16b
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
sub x7, x7, #1
cbnz x7, 22b
ext v1.16b, v1.16b, v1.16b, #4
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #12
zip1 v16.4s, v0.4s, v1.4s
zip2 v17.4s, v0.4s, v1.4s
zip1 v18.4s, v2.4s, v3.4s
zip2 v19.4s, v2.4s, v3.4s
zip1 v0.2d, v16.2d, v18.2d
zip2 v1.2d, v16.2d, v18.2d
zip1 v2.2d, v17.2d, v19.2d
zip2 v3.2d, v17.2d, v19.2d
ext v1.16b, v1.16b, v1.16b, #12
ext v2.16b, v2.16b, v2.16b, #8
ext v3.16b, v3.16b, v3.16b, #4
add v0.4s, v0.4s, v4.4s
add v1.4s, v1.4s, v5.4s
add v2.4s, v2.4s, v6.4s
add v3.4s, v3.4s, v7.4s
str q0, [x6, #0]
str q1, [x6, #16]
str q2, [x6, #32]
str q3, [x6, #48]
add x0, x0, #64
add x2, x2, #64
add x6, x6, #64
sub x1, x1, #1
cbnz x1, 20b
ret
.p2align 6
.globl trial_bm_resident_mem
trial_bm_resident_mem:
dup v24.2d, x19
dup v25.2d, x20
dup v26.2d, x21
dup v27.2d, x22
add x21, x1, #0
add x19, x2, #0
lsl x22, x1, #6
add x20, x2, x22
lsl x22, x1, #7
add x22, x0, x22
sub x22, x22, #64
ldr w2, [x22, #0]
ldr w3, [x22, #4]
ldr w4, [x22, #8]
ldr w5, [x22, #12]
ldr w6, [x22, #16]
ldr w7, [x22, #20]
ldr w8, [x22, #24]
ldr w9, [x22, #28]
ldr w10, [x22, #32]
ldr w11, [x22, #36]
ldr w12, [x22, #40]
ldr w13, [x22, #44]
ldr w14, [x22, #48]
ldr w15, [x22, #52]
ldr w16, [x22, #56]
ldr w17, [x22, #60]
20:
ldr w22, [x0, #0]
eor w2, w2, w22
str w2, [x19, #0]
ldr w22, [x0, #4]
eor w3, w3, w22
str w3, [x19, #4]
ldr w22, [x0, #8]
eor w4, w4, w22
str w4, [x19, #8]
ldr w22, [x0, #12]
eor w5, w5, w22
str w5, [x19, #12]
ldr w22, [x0, #16]
eor w6, w6, w22
str w6, [x19, #16]
ldr w22, [x0, #20]
eor w7, w7, w22
str w7, [x19, #20]
ldr w22, [x0, #24]
eor w8, w8, w22
str w8, [x19, #24]
ldr w22, [x0, #28]
eor w9, w9, w22
str w9, [x19, #28]
ldr w22, [x0, #32]
eor w10, w10, w22
str w10, [x19, #32]
ldr w22, [x0, #36]
eor w11, w11, w22
str w11, [x19, #36]
ldr w22, [x0, #40]
eor w12, w12, w22
str w12, [x19, #40]
ldr w22, [x0, #44]
eor w13, w13, w22
str w13, [x19, #44]
ldr w22, [x0, #48]
eor w14, w14, w22
str w14, [x19, #48]
ldr w22, [x0, #52]
eor w15, w15, w22
str w15, [x19, #52]
ldr w22, [x0, #56]
eor w16, w16, w22
str w16, [x19, #56]
ldr w22, [x0, #60]
eor w17, w17, w22
str w17, [x19, #60]
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
ldr w1, [x19, #0]
add w2, w2, w1
str w2, [x19, #0]
ldr w1, [x19, #4]
add w3, w3, w1
str w3, [x19, #4]
ldr w1, [x19, #8]
add w4, w4, w1
str w4, [x19, #8]
ldr w1, [x19, #12]
add w5, w5, w1
str w5, [x19, #12]
ldr w1, [x19, #16]
add w6, w6, w1
str w6, [x19, #16]
ldr w1, [x19, #20]
add w7, w7, w1
str w7, [x19, #20]
ldr w1, [x19, #24]
add w8, w8, w1
str w8, [x19, #24]
ldr w1, [x19, #28]
add w9, w9, w1
str w9, [x19, #28]
ldr w1, [x19, #32]
add w10, w10, w1
str w10, [x19, #32]
ldr w1, [x19, #36]
add w11, w11, w1
str w11, [x19, #36]
ldr w1, [x19, #40]
add w12, w12, w1
str w12, [x19, #40]
ldr w1, [x19, #44]
add w13, w13, w1
str w13, [x19, #44]
ldr w1, [x19, #48]
add w14, w14, w1
str w14, [x19, #48]
ldr w1, [x19, #52]
add w15, w15, w1
str w15, [x19, #52]
ldr w1, [x19, #56]
add w16, w16, w1
str w16, [x19, #56]
ldr w1, [x19, #60]
add w17, w17, w1
str w17, [x19, #60]
add x0, x0, #64
ldr w22, [x0, #0]
eor w2, w2, w22
str w2, [x20, #0]
ldr w22, [x0, #4]
eor w3, w3, w22
str w3, [x20, #4]
ldr w22, [x0, #8]
eor w4, w4, w22
str w4, [x20, #8]
ldr w22, [x0, #12]
eor w5, w5, w22
str w5, [x20, #12]
ldr w22, [x0, #16]
eor w6, w6, w22
str w6, [x20, #16]
ldr w22, [x0, #20]
eor w7, w7, w22
str w7, [x20, #20]
ldr w22, [x0, #24]
eor w8, w8, w22
str w8, [x20, #24]
ldr w22, [x0, #28]
eor w9, w9, w22
str w9, [x20, #28]
ldr w22, [x0, #32]
eor w10, w10, w22
str w10, [x20, #32]
ldr w22, [x0, #36]
eor w11, w11, w22
str w11, [x20, #36]
ldr w22, [x0, #40]
eor w12, w12, w22
str w12, [x20, #40]
ldr w22, [x0, #44]
eor w13, w13, w22
str w13, [x20, #44]
ldr w22, [x0, #48]
eor w14, w14, w22
str w14, [x20, #48]
ldr w22, [x0, #52]
eor w15, w15, w22
str w15, [x20, #52]
ldr w22, [x0, #56]
eor w16, w16, w22
str w16, [x20, #56]
ldr w22, [x0, #60]
eor w17, w17, w22
str w17, [x20, #60]
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
ldr w1, [x20, #0]
add w2, w2, w1
str w2, [x20, #0]
ldr w1, [x20, #4]
add w3, w3, w1
str w3, [x20, #4]
ldr w1, [x20, #8]
add w4, w4, w1
str w4, [x20, #8]
ldr w1, [x20, #12]
add w5, w5, w1
str w5, [x20, #12]
ldr w1, [x20, #16]
add w6, w6, w1
str w6, [x20, #16]
ldr w1, [x20, #20]
add w7, w7, w1
str w7, [x20, #20]
ldr w1, [x20, #24]
add w8, w8, w1
str w8, [x20, #24]
ldr w1, [x20, #28]
add w9, w9, w1
str w9, [x20, #28]
ldr w1, [x20, #32]
add w10, w10, w1
str w10, [x20, #32]
ldr w1, [x20, #36]
add w11, w11, w1
str w11, [x20, #36]
ldr w1, [x20, #40]
add w12, w12, w1
str w12, [x20, #40]
ldr w1, [x20, #44]
add w13, w13, w1
str w13, [x20, #44]
ldr w1, [x20, #48]
add w14, w14, w1
str w14, [x20, #48]
ldr w1, [x20, #52]
add w15, w15, w1
str w15, [x20, #52]
ldr w1, [x20, #56]
add w16, w16, w1
str w16, [x20, #56]
ldr w1, [x20, #60]
add w17, w17, w1
str w17, [x20, #60]
add x0, x0, #64
add x19, x19, #64
add x20, x20, #64
sub x21, x21, #1
cbnz x21, 20b
umov x19, v24.d[0]
umov x20, v25.d[0]
umov x21, v26.d[0]
umov x22, v27.d[0]
ret
.p2align 6
.globl trial_bm_resident_ins
trial_bm_resident_ins:
dup v24.2d, x19
dup v25.2d, x20
dup v26.2d, x21
dup v27.2d, x22
add x21, x1, #0
add x19, x2, #0
lsl x22, x1, #6
add x20, x2, x22
lsl x22, x1, #7
add x22, x0, x22
sub x22, x22, #64
ldr w2, [x22, #0]
ldr w3, [x22, #4]
ldr w4, [x22, #8]
ldr w5, [x22, #12]
ldr w6, [x22, #16]
ldr w7, [x22, #20]
ldr w8, [x22, #24]
ldr w9, [x22, #28]
ldr w10, [x22, #32]
ldr w11, [x22, #36]
ldr w12, [x22, #40]
ldr w13, [x22, #44]
ldr w14, [x22, #48]
ldr w15, [x22, #52]
ldr w16, [x22, #56]
ldr w17, [x22, #60]
20:
ldr w22, [x0, #0]
eor w2, w2, w22
mov v0.s[0], w2
ldr w22, [x0, #4]
eor w3, w3, w22
mov v0.s[1], w3
ldr w22, [x0, #8]
eor w4, w4, w22
mov v0.s[2], w4
ldr w22, [x0, #12]
eor w5, w5, w22
mov v0.s[3], w5
ldr w22, [x0, #16]
eor w6, w6, w22
mov v1.s[0], w6
ldr w22, [x0, #20]
eor w7, w7, w22
mov v1.s[1], w7
ldr w22, [x0, #24]
eor w8, w8, w22
mov v1.s[2], w8
ldr w22, [x0, #28]
eor w9, w9, w22
mov v1.s[3], w9
ldr w22, [x0, #32]
eor w10, w10, w22
mov v2.s[0], w10
ldr w22, [x0, #36]
eor w11, w11, w22
mov v2.s[1], w11
ldr w22, [x0, #40]
eor w12, w12, w22
mov v2.s[2], w12
ldr w22, [x0, #44]
eor w13, w13, w22
mov v2.s[3], w13
ldr w22, [x0, #48]
eor w14, w14, w22
mov v3.s[0], w14
ldr w22, [x0, #52]
eor w15, w15, w22
mov v3.s[1], w15
ldr w22, [x0, #56]
eor w16, w16, w22
mov v3.s[2], w16
ldr w22, [x0, #60]
eor w17, w17, w22
mov v3.s[3], w17
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
umov w1, v0.s[0]
add w2, w2, w1
str w2, [x19, #0]
umov w1, v0.s[1]
add w3, w3, w1
str w3, [x19, #4]
umov w1, v0.s[2]
add w4, w4, w1
str w4, [x19, #8]
umov w1, v0.s[3]
add w5, w5, w1
str w5, [x19, #12]
umov w1, v1.s[0]
add w6, w6, w1
str w6, [x19, #16]
umov w1, v1.s[1]
add w7, w7, w1
str w7, [x19, #20]
umov w1, v1.s[2]
add w8, w8, w1
str w8, [x19, #24]
umov w1, v1.s[3]
add w9, w9, w1
str w9, [x19, #28]
umov w1, v2.s[0]
add w10, w10, w1
str w10, [x19, #32]
umov w1, v2.s[1]
add w11, w11, w1
str w11, [x19, #36]
umov w1, v2.s[2]
add w12, w12, w1
str w12, [x19, #40]
umov w1, v2.s[3]
add w13, w13, w1
str w13, [x19, #44]
umov w1, v3.s[0]
add w14, w14, w1
str w14, [x19, #48]
umov w1, v3.s[1]
add w15, w15, w1
str w15, [x19, #52]
umov w1, v3.s[2]
add w16, w16, w1
str w16, [x19, #56]
umov w1, v3.s[3]
add w17, w17, w1
str w17, [x19, #60]
add x0, x0, #64
ldr w22, [x0, #0]
eor w2, w2, w22
mov v0.s[0], w2
ldr w22, [x0, #4]
eor w3, w3, w22
mov v0.s[1], w3
ldr w22, [x0, #8]
eor w4, w4, w22
mov v0.s[2], w4
ldr w22, [x0, #12]
eor w5, w5, w22
mov v0.s[3], w5
ldr w22, [x0, #16]
eor w6, w6, w22
mov v1.s[0], w6
ldr w22, [x0, #20]
eor w7, w7, w22
mov v1.s[1], w7
ldr w22, [x0, #24]
eor w8, w8, w22
mov v1.s[2], w8
ldr w22, [x0, #28]
eor w9, w9, w22
mov v1.s[3], w9
ldr w22, [x0, #32]
eor w10, w10, w22
mov v2.s[0], w10
ldr w22, [x0, #36]
eor w11, w11, w22
mov v2.s[1], w11
ldr w22, [x0, #40]
eor w12, w12, w22
mov v2.s[2], w12
ldr w22, [x0, #44]
eor w13, w13, w22
mov v2.s[3], w13
ldr w22, [x0, #48]
eor w14, w14, w22
mov v3.s[0], w14
ldr w22, [x0, #52]
eor w15, w15, w22
mov v3.s[1], w15
ldr w22, [x0, #56]
eor w16, w16, w22
mov v3.s[2], w16
ldr w22, [x0, #60]
eor w17, w17, w22
mov v3.s[3], w17
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
umov w1, v0.s[0]
add w2, w2, w1
str w2, [x20, #0]
umov w1, v0.s[1]
add w3, w3, w1
str w3, [x20, #4]
umov w1, v0.s[2]
add w4, w4, w1
str w4, [x20, #8]
umov w1, v0.s[3]
add w5, w5, w1
str w5, [x20, #12]
umov w1, v1.s[0]
add w6, w6, w1
str w6, [x20, #16]
umov w1, v1.s[1]
add w7, w7, w1
str w7, [x20, #20]
umov w1, v1.s[2]
add w8, w8, w1
str w8, [x20, #24]
umov w1, v1.s[3]
add w9, w9, w1
str w9, [x20, #28]
umov w1, v2.s[0]
add w10, w10, w1
str w10, [x20, #32]
umov w1, v2.s[1]
add w11, w11, w1
str w11, [x20, #36]
umov w1, v2.s[2]
add w12, w12, w1
str w12, [x20, #40]
umov w1, v2.s[3]
add w13, w13, w1
str w13, [x20, #44]
umov w1, v3.s[0]
add w14, w14, w1
str w14, [x20, #48]
umov w1, v3.s[1]
add w15, w15, w1
str w15, [x20, #52]
umov w1, v3.s[2]
add w16, w16, w1
str w16, [x20, #56]
umov w1, v3.s[3]
add w17, w17, w1
str w17, [x20, #60]
add x0, x0, #64
add x19, x19, #64
add x20, x20, #64
sub x21, x21, #1
cbnz x21, 20b
umov x19, v24.d[0]
umov x20, v25.d[0]
umov x21, v26.d[0]
umov x22, v27.d[0]
ret
.p2align 6
.globl trial_bm_resident_dup
trial_bm_resident_dup:
dup v24.2d, x19
dup v25.2d, x20
dup v26.2d, x21
dup v27.2d, x22
add x21, x1, #0
add x19, x2, #0
lsl x22, x1, #6
add x20, x2, x22
lsl x22, x1, #7
add x22, x0, x22
sub x22, x22, #64
ldr w2, [x22, #0]
ldr w3, [x22, #4]
ldr w4, [x22, #8]
ldr w5, [x22, #12]
ldr w6, [x22, #16]
ldr w7, [x22, #20]
ldr w8, [x22, #24]
ldr w9, [x22, #28]
ldr w10, [x22, #32]
ldr w11, [x22, #36]
ldr w12, [x22, #40]
ldr w13, [x22, #44]
ldr w14, [x22, #48]
ldr w15, [x22, #52]
ldr w16, [x22, #56]
ldr w17, [x22, #60]
20:
ldr w22, [x0, #0]
eor w2, w2, w22
dup v0.4s, w2
ldr w22, [x0, #4]
eor w3, w3, w22
dup v1.4s, w3
ldr w22, [x0, #8]
eor w4, w4, w22
dup v2.4s, w4
ldr w22, [x0, #12]
eor w5, w5, w22
dup v3.4s, w5
ldr w22, [x0, #16]
eor w6, w6, w22
dup v4.4s, w6
ldr w22, [x0, #20]
eor w7, w7, w22
dup v5.4s, w7
ldr w22, [x0, #24]
eor w8, w8, w22
dup v6.4s, w8
ldr w22, [x0, #28]
eor w9, w9, w22
dup v7.4s, w9
ldr w22, [x0, #32]
eor w10, w10, w22
dup v16.4s, w10
ldr w22, [x0, #36]
eor w11, w11, w22
dup v17.4s, w11
ldr w22, [x0, #40]
eor w12, w12, w22
dup v18.4s, w12
ldr w22, [x0, #44]
eor w13, w13, w22
dup v19.4s, w13
ldr w22, [x0, #48]
eor w14, w14, w22
dup v20.4s, w14
ldr w22, [x0, #52]
eor w15, w15, w22
dup v21.4s, w15
ldr w22, [x0, #56]
eor w16, w16, w22
dup v22.4s, w16
ldr w22, [x0, #60]
eor w17, w17, w22
dup v23.4s, w17
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
umov w1, v0.s[0]
add w2, w2, w1
str w2, [x19, #0]
umov w1, v1.s[0]
add w3, w3, w1
str w3, [x19, #4]
umov w1, v2.s[0]
add w4, w4, w1
str w4, [x19, #8]
umov w1, v3.s[0]
add w5, w5, w1
str w5, [x19, #12]
umov w1, v4.s[0]
add w6, w6, w1
str w6, [x19, #16]
umov w1, v5.s[0]
add w7, w7, w1
str w7, [x19, #20]
umov w1, v6.s[0]
add w8, w8, w1
str w8, [x19, #24]
umov w1, v7.s[0]
add w9, w9, w1
str w9, [x19, #28]
umov w1, v16.s[0]
add w10, w10, w1
str w10, [x19, #32]
umov w1, v17.s[0]
add w11, w11, w1
str w11, [x19, #36]
umov w1, v18.s[0]
add w12, w12, w1
str w12, [x19, #40]
umov w1, v19.s[0]
add w13, w13, w1
str w13, [x19, #44]
umov w1, v20.s[0]
add w14, w14, w1
str w14, [x19, #48]
umov w1, v21.s[0]
add w15, w15, w1
str w15, [x19, #52]
umov w1, v22.s[0]
add w16, w16, w1
str w16, [x19, #56]
umov w1, v23.s[0]
add w17, w17, w1
str w17, [x19, #60]
add x0, x0, #64
ldr w22, [x0, #0]
eor w2, w2, w22
dup v0.4s, w2
ldr w22, [x0, #4]
eor w3, w3, w22
dup v1.4s, w3
ldr w22, [x0, #8]
eor w4, w4, w22
dup v2.4s, w4
ldr w22, [x0, #12]
eor w5, w5, w22
dup v3.4s, w5
ldr w22, [x0, #16]
eor w6, w6, w22
dup v4.4s, w6
ldr w22, [x0, #20]
eor w7, w7, w22
dup v5.4s, w7
ldr w22, [x0, #24]
eor w8, w8, w22
dup v6.4s, w8
ldr w22, [x0, #28]
eor w9, w9, w22
dup v7.4s, w9
ldr w22, [x0, #32]
eor w10, w10, w22
dup v16.4s, w10
ldr w22, [x0, #36]
eor w11, w11, w22
dup v17.4s, w11
ldr w22, [x0, #40]
eor w12, w12, w22
dup v18.4s, w12
ldr w22, [x0, #44]
eor w13, w13, w22
dup v19.4s, w13
ldr w22, [x0, #48]
eor w14, w14, w22
dup v20.4s, w14
ldr w22, [x0, #52]
eor w15, w15, w22
dup v21.4s, w15
ldr w22, [x0, #56]
eor w16, w16, w22
dup v22.4s, w16
ldr w22, [x0, #60]
eor w17, w17, w22
dup v23.4s, w17
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
umov w1, v0.s[0]
add w2, w2, w1
str w2, [x20, #0]
umov w1, v1.s[0]
add w3, w3, w1
str w3, [x20, #4]
umov w1, v2.s[0]
add w4, w4, w1
str w4, [x20, #8]
umov w1, v3.s[0]
add w5, w5, w1
str w5, [x20, #12]
umov w1, v4.s[0]
add w6, w6, w1
str w6, [x20, #16]
umov w1, v5.s[0]
add w7, w7, w1
str w7, [x20, #20]
umov w1, v6.s[0]
add w8, w8, w1
str w8, [x20, #24]
umov w1, v7.s[0]
add w9, w9, w1
str w9, [x20, #28]
umov w1, v16.s[0]
add w10, w10, w1
str w10, [x20, #32]
umov w1, v17.s[0]
add w11, w11, w1
str w11, [x20, #36]
umov w1, v18.s[0]
add w12, w12, w1
str w12, [x20, #40]
umov w1, v19.s[0]
add w13, w13, w1
str w13, [x20, #44]
umov w1, v20.s[0]
add w14, w14, w1
str w14, [x20, #48]
umov w1, v21.s[0]
add w15, w15, w1
str w15, [x20, #52]
umov w1, v22.s[0]
add w16, w16, w1
str w16, [x20, #56]
umov w1, v23.s[0]
add w17, w17, w1
str w17, [x20, #60]
add x0, x0, #64
add x19, x19, #64
add x20, x20, #64
sub x21, x21, #1
cbnz x21, 20b
umov x19, v24.d[0]
umov x20, v25.d[0]
umov x21, v26.d[0]
umov x22, v27.d[0]
ret
.p2align 6
.globl trial_bm_resident_ref
trial_bm_resident_ref:
str x19, [x4, #64]
str x20, [x4, #72]
str x21, [x4, #80]
str x23, [x4, #88]
str x24, [x4, #96]
str x22, [x4, #104]
add x23, x1, #0
add x19, x0, #0
add x20, x2, #0
add x22, x4, #0
lsl x9, x1, #6
add x21, x2, x9
lsl x9, x1, #7
add x24, x0, x9
sub x24, x24, #64
ldr w2, [x24, #0]
ldr w3, [x24, #4]
ldr w4, [x24, #8]
ldr w5, [x24, #12]
ldr w6, [x24, #16]
ldr w7, [x24, #20]
ldr w8, [x24, #24]
ldr w9, [x24, #28]
ldr w10, [x24, #32]
ldr w11, [x24, #36]
ldr w12, [x24, #40]
ldr w13, [x24, #44]
ldr w14, [x24, #48]
ldr w15, [x24, #52]
ldr w16, [x24, #56]
ldr w17, [x24, #60]
20:
ldr w1, [x19, #0]
eor w2, w2, w1
str w2, [x20, #0]
ldr w1, [x19, #4]
eor w3, w3, w1
str w3, [x20, #4]
ldr w1, [x19, #8]
eor w4, w4, w1
str w4, [x20, #8]
ldr w1, [x19, #12]
eor w5, w5, w1
str w5, [x20, #12]
ldr w1, [x19, #16]
eor w6, w6, w1
str w6, [x20, #16]
ldr w1, [x19, #20]
eor w7, w7, w1
str w7, [x20, #20]
ldr w1, [x19, #24]
eor w8, w8, w1
str w8, [x20, #24]
ldr w1, [x19, #28]
eor w9, w9, w1
str w9, [x20, #28]
ldr w1, [x19, #32]
eor w10, w10, w1
str w10, [x20, #32]
ldr w1, [x19, #36]
eor w11, w11, w1
str w11, [x20, #36]
ldr w1, [x19, #40]
eor w12, w12, w1
str w12, [x20, #40]
ldr w1, [x19, #44]
eor w13, w13, w1
str w13, [x20, #44]
ldr w1, [x19, #48]
eor w14, w14, w1
str w14, [x20, #48]
ldr w1, [x19, #52]
eor w15, w15, w1
str w15, [x20, #52]
ldr w1, [x19, #56]
eor w16, w16, w1
str w16, [x20, #56]
ldr w1, [x19, #60]
eor w17, w17, w1
str w17, [x20, #60]
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
ldr w1, [x20, #0]
add w2, w2, w1
str w2, [x20, #0]
ldr w1, [x20, #4]
add w3, w3, w1
str w3, [x20, #4]
ldr w1, [x20, #8]
add w4, w4, w1
str w4, [x20, #8]
ldr w1, [x20, #12]
add w5, w5, w1
str w5, [x20, #12]
ldr w1, [x20, #16]
add w6, w6, w1
str w6, [x20, #16]
ldr w1, [x20, #20]
add w7, w7, w1
str w7, [x20, #20]
ldr w1, [x20, #24]
add w8, w8, w1
str w8, [x20, #24]
ldr w1, [x20, #28]
add w9, w9, w1
str w9, [x20, #28]
ldr w1, [x20, #32]
add w10, w10, w1
str w10, [x20, #32]
ldr w1, [x20, #36]
add w11, w11, w1
str w11, [x20, #36]
ldr w1, [x20, #40]
add w12, w12, w1
str w12, [x20, #40]
ldr w1, [x20, #44]
add w13, w13, w1
str w13, [x20, #44]
ldr w1, [x20, #48]
add w14, w14, w1
str w14, [x20, #48]
ldr w1, [x20, #52]
add w15, w15, w1
str w15, [x20, #52]
ldr w1, [x20, #56]
add w16, w16, w1
str w16, [x20, #56]
ldr w1, [x20, #60]
add w17, w17, w1
str w17, [x20, #60]
add x19, x19, #64
ldr w1, [x19, #0]
eor w2, w2, w1
str w2, [x21, #0]
ldr w1, [x19, #4]
eor w3, w3, w1
str w3, [x21, #4]
ldr w1, [x19, #8]
eor w4, w4, w1
str w4, [x21, #8]
ldr w1, [x19, #12]
eor w5, w5, w1
str w5, [x21, #12]
ldr w1, [x19, #16]
eor w6, w6, w1
str w6, [x21, #16]
ldr w1, [x19, #20]
eor w7, w7, w1
str w7, [x21, #20]
ldr w1, [x19, #24]
eor w8, w8, w1
str w8, [x21, #24]
ldr w1, [x19, #28]
eor w9, w9, w1
str w9, [x21, #28]
ldr w1, [x19, #32]
eor w10, w10, w1
str w10, [x21, #32]
ldr w1, [x19, #36]
eor w11, w11, w1
str w11, [x21, #36]
ldr w1, [x19, #40]
eor w12, w12, w1
str w12, [x21, #40]
ldr w1, [x19, #44]
eor w13, w13, w1
str w13, [x21, #44]
ldr w1, [x19, #48]
eor w14, w14, w1
str w14, [x21, #48]
ldr w1, [x19, #52]
eor w15, w15, w1
str w15, [x21, #52]
ldr w1, [x19, #56]
eor w16, w16, w1
str w16, [x21, #56]
ldr w1, [x19, #60]
eor w17, w17, w1
str w17, [x21, #60]
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w14
ror w1, w1, #25
eor w6, w6, w1
add w1, w6, w2
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w6
ror w1, w1, #19
eor w14, w14, w1
add w1, w14, w10
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w3
ror w1, w1, #25
eor w11, w11, w1
add w1, w11, w7
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w11
ror w1, w1, #19
eor w3, w3, w1
add w1, w3, w15
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w8
ror w1, w1, #25
eor w16, w16, w1
add w1, w16, w12
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w16
ror w1, w1, #19
eor w8, w8, w1
add w1, w8, w4
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w13
ror w1, w1, #25
eor w5, w5, w1
add w1, w5, w17
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w5
ror w1, w1, #19
eor w13, w13, w1
add w1, w13, w9
ror w1, w1, #14
eor w17, w17, w1
add w1, w2, w5
ror w1, w1, #25
eor w3, w3, w1
add w1, w3, w2
ror w1, w1, #23
eor w4, w4, w1
add w1, w4, w3
ror w1, w1, #19
eor w5, w5, w1
add w1, w5, w4
ror w1, w1, #14
eor w2, w2, w1
add w1, w7, w6
ror w1, w1, #25
eor w8, w8, w1
add w1, w8, w7
ror w1, w1, #23
eor w9, w9, w1
add w1, w9, w8
ror w1, w1, #19
eor w6, w6, w1
add w1, w6, w9
ror w1, w1, #14
eor w7, w7, w1
add w1, w12, w11
ror w1, w1, #25
eor w13, w13, w1
add w1, w13, w12
ror w1, w1, #23
eor w10, w10, w1
add w1, w10, w13
ror w1, w1, #19
eor w11, w11, w1
add w1, w11, w10
ror w1, w1, #14
eor w12, w12, w1
add w1, w17, w16
ror w1, w1, #25
eor w14, w14, w1
add w1, w14, w17
ror w1, w1, #23
eor w15, w15, w1
add w1, w15, w14
ror w1, w1, #19
eor w16, w16, w1
add w1, w16, w15
ror w1, w1, #14
eor w17, w17, w1
ldr w1, [x21, #0]
add w2, w2, w1
str w2, [x21, #0]
ldr w1, [x21, #4]
add w3, w3, w1
str w3, [x21, #4]
ldr w1, [x21, #8]
add w4, w4, w1
str w4, [x21, #8]
ldr w1, [x21, #12]
add w5, w5, w1
str w5, [x21, #12]
ldr w1, [x21, #16]
add w6, w6, w1
str w6, [x21, #16]
ldr w1, [x21, #20]
add w7, w7, w1
str w7, [x21, #20]
ldr w1, [x21, #24]
add w8, w8, w1
str w8, [x21, #24]
ldr w1, [x21, #28]
add w9, w9, w1
str w9, [x21, #28]
ldr w1, [x21, #32]
add w10, w10, w1
str w10, [x21, #32]
ldr w1, [x21, #36]
add w11, w11, w1
str w11, [x21, #36]
ldr w1, [x21, #40]
add w12, w12, w1
str w12, [x21, #40]
ldr w1, [x21, #44]
add w13, w13, w1
str w13, [x21, #44]
ldr w1, [x21, #48]
add w14, w14, w1
str w14, [x21, #48]
ldr w1, [x21, #52]
add w15, w15, w1
str w15, [x21, #52]
ldr w1, [x21, #56]
add w16, w16, w1
str w16, [x21, #56]
ldr w1, [x21, #60]
add w17, w17, w1
str w17, [x21, #60]
add x19, x19, #64
add x24, x21, #0
add x20, x20, #64
add x21, x21, #64
sub x23, x23, #1
cbnz x23, 20b
ldr x19, [x22, #64]
ldr x20, [x22, #72]
ldr x21, [x22, #80]
ldr x23, [x22, #88]
ldr x24, [x22, #96]
ldr x22, [x22, #104]
ret
.p2align 6
.globl trial_bm_fold
trial_bm_fold:
str x30, [sp, #-16]!
str x19, [x4, #64]
str x20, [x4, #72]
str x21, [x4, #80]
str x23, [x4, #88]
str x24, [x4, #96]
str x22, [x4, #104]
add x23, x1, #0
add x19, x0, #0
add x20, x2, #0
add x22, x4, #0
lsl x9, x1, #6
add x21, x2, x9
lsl x9, x1, #7
add x24, x0, x9
sub x24, x24, #64
20:
ldr x9, [x24, #0]
ldr x10, [x19, #0]
eor x9, x9, x10
str x9, [x20, #0]
ldr x9, [x24, #8]
ldr x10, [x19, #8]
eor x9, x9, x10
str x9, [x20, #8]
ldr x9, [x24, #16]
ldr x10, [x19, #16]
eor x9, x9, x10
str x9, [x20, #16]
ldr x9, [x24, #24]
ldr x10, [x19, #24]
eor x9, x9, x10
str x9, [x20, #24]
ldr x9, [x24, #32]
ldr x10, [x19, #32]
eor x9, x9, x10
str x9, [x20, #32]
ldr x9, [x24, #40]
ldr x10, [x19, #40]
eor x9, x9, x10
str x9, [x20, #40]
ldr x9, [x24, #48]
ldr x10, [x19, #48]
eor x9, x9, x10
str x9, [x20, #48]
ldr x9, [x24, #56]
ldr x10, [x19, #56]
eor x9, x9, x10
str x9, [x20, #56]
add x0, x20, #0
add x1, x22, #0
bl trial_fold
add x19, x19, #64
ldr x9, [x20, #0]
ldr x10, [x19, #0]
eor x9, x9, x10
str x9, [x21, #0]
ldr x9, [x20, #8]
ldr x10, [x19, #8]
eor x9, x9, x10
str x9, [x21, #8]
ldr x9, [x20, #16]
ldr x10, [x19, #16]
eor x9, x9, x10
str x9, [x21, #16]
ldr x9, [x20, #24]
ldr x10, [x19, #24]
eor x9, x9, x10
str x9, [x21, #24]
ldr x9, [x20, #32]
ldr x10, [x19, #32]
eor x9, x9, x10
str x9, [x21, #32]
ldr x9, [x20, #40]
ldr x10, [x19, #40]
eor x9, x9, x10
str x9, [x21, #40]
ldr x9, [x20, #48]
ldr x10, [x19, #48]
eor x9, x9, x10
str x9, [x21, #48]
ldr x9, [x20, #56]
ldr x10, [x19, #56]
eor x9, x9, x10
str x9, [x21, #56]
add x0, x21, #0
add x1, x22, #0
bl trial_fold
add x24, x21, #0
add x19, x19, #64
add x20, x20, #64
add x21, x21, #64
sub x23, x23, #1
cbnz x23, 20b
ldr x19, [x22, #64]
ldr x20, [x22, #72]
ldr x21, [x22, #80]
ldr x23, [x22, #88]
ldr x24, [x22, #96]
ldr x22, [x22, #104]
ldr x30, [sp], #16
ret
.p2align 6
.globl trial_bm_fold_vcopy
trial_bm_fold_vcopy:
str x30, [sp, #-16]!
str x19, [x4, #64]
str x20, [x4, #72]
str x21, [x4, #80]
str x23, [x4, #88]
str x24, [x4, #96]
str x22, [x4, #104]
add x23, x1, #0
add x19, x0, #0
add x20, x2, #0
add x22, x4, #0
lsl x9, x1, #6
add x21, x2, x9
lsl x9, x1, #7
add x24, x0, x9
sub x24, x24, #64
20:
ldr q0, [x24, #0]
ldr q1, [x19, #0]
eor v0.16b, v0.16b, v1.16b
str q0, [x20, #0]
ldr q0, [x24, #16]
ldr q1, [x19, #16]
eor v0.16b, v0.16b, v1.16b
str q0, [x20, #16]
ldr q0, [x24, #32]
ldr q1, [x19, #32]
eor v0.16b, v0.16b, v1.16b
str q0, [x20, #32]
ldr q0, [x24, #48]
ldr q1, [x19, #48]
eor v0.16b, v0.16b, v1.16b
str q0, [x20, #48]
add x0, x20, #0
add x1, x22, #0
bl trial_fold
add x19, x19, #64
ldr q0, [x20, #0]
ldr q1, [x19, #0]
eor v0.16b, v0.16b, v1.16b
str q0, [x21, #0]
ldr q0, [x20, #16]
ldr q1, [x19, #16]
eor v0.16b, v0.16b, v1.16b
str q0, [x21, #16]
ldr q0, [x20, #32]
ldr q1, [x19, #32]
eor v0.16b, v0.16b, v1.16b
str q0, [x21, #32]
ldr q0, [x20, #48]
ldr q1, [x19, #48]
eor v0.16b, v0.16b, v1.16b
str q0, [x21, #48]
add x0, x21, #0
add x1, x22, #0
bl trial_fold
add x24, x21, #0
add x19, x19, #64
add x20, x20, #64
add x21, x21, #64
sub x23, x23, #1
cbnz x23, 20b
ldr x19, [x22, #64]
ldr x20, [x22, #72]
ldr x21, [x22, #80]
ldr x23, [x22, #88]
ldr x24, [x22, #96]
ldr x22, [x22, #104]
ldr x30, [sp], #16
ret
.p2align 6
.globl trial_bm_fold_inline
trial_bm_fold_inline:
str x19, [x4, #64]
str x20, [x4, #72]
str x21, [x4, #80]
str x23, [x4, #88]
str x24, [x4, #96]
str x22, [x4, #104]
add x23, x1, #0
add x19, x0, #0
add x20, x2, #0
add x22, x4, #0
lsl x9, x1, #6
add x21, x2, x9
lsl x9, x1, #7
add x24, x0, x9
sub x24, x24, #64
20:
ldr q0, [x24, #0]
ldr q1, [x19, #0]
eor v0.16b, v0.16b, v1.16b
str q0, [x20, #0]
ldr q0, [x24, #16]
ldr q1, [x19, #16]
eor v0.16b, v0.16b, v1.16b
str q0, [x20, #16]
ldr q0, [x24, #32]
ldr q1, [x19, #32]
eor v0.16b, v0.16b, v1.16b
str q0, [x20, #32]
ldr q0, [x24, #48]
ldr q1, [x19, #48]
eor v0.16b, v0.16b, v1.16b
str q0, [x20, #48]
add x0, x20, #0
ldr w2, [x0, #0]
ldr w3, [x0, #4]
ldr w4, [x0, #8]
ldr w5, [x0, #12]
ldr w6, [x0, #16]
ldr w7, [x0, #20]
ldr w8, [x0, #24]
ldr w9, [x0, #28]
ldr w10, [x0, #32]
ldr w11, [x0, #36]
ldr w12, [x0, #40]
ldr w13, [x0, #44]
ldr w14, [x0, #48]
ldr w15, [x0, #52]
ldr w16, [x0, #56]
ldr w17, [x0, #60]
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
ldr w1, [x0, #0]
add w2, w2, w1
str w2, [x0, #0]
ldr w1, [x0, #4]
add w3, w3, w1
str w3, [x0, #4]
ldr w1, [x0, #8]
add w4, w4, w1
str w4, [x0, #8]
ldr w1, [x0, #12]
add w5, w5, w1
str w5, [x0, #12]
ldr w1, [x0, #16]
add w6, w6, w1
str w6, [x0, #16]
ldr w1, [x0, #20]
add w7, w7, w1
str w7, [x0, #20]
ldr w1, [x0, #24]
add w8, w8, w1
str w8, [x0, #24]
ldr w1, [x0, #28]
add w9, w9, w1
str w9, [x0, #28]
ldr w1, [x0, #32]
add w10, w10, w1
str w10, [x0, #32]
ldr w1, [x0, #36]
add w11, w11, w1
str w11, [x0, #36]
ldr w1, [x0, #40]
add w12, w12, w1
str w12, [x0, #40]
ldr w1, [x0, #44]
add w13, w13, w1
str w13, [x0, #44]
ldr w1, [x0, #48]
add w14, w14, w1
str w14, [x0, #48]
ldr w1, [x0, #52]
add w15, w15, w1
str w15, [x0, #52]
ldr w1, [x0, #56]
add w16, w16, w1
str w16, [x0, #56]
ldr w1, [x0, #60]
add w17, w17, w1
str w17, [x0, #60]
add x19, x19, #64
ldr q0, [x20, #0]
ldr q1, [x19, #0]
eor v0.16b, v0.16b, v1.16b
str q0, [x21, #0]
ldr q0, [x20, #16]
ldr q1, [x19, #16]
eor v0.16b, v0.16b, v1.16b
str q0, [x21, #16]
ldr q0, [x20, #32]
ldr q1, [x19, #32]
eor v0.16b, v0.16b, v1.16b
str q0, [x21, #32]
ldr q0, [x20, #48]
ldr q1, [x19, #48]
eor v0.16b, v0.16b, v1.16b
str q0, [x21, #48]
add x0, x21, #0
ldr w2, [x0, #0]
ldr w3, [x0, #4]
ldr w4, [x0, #8]
ldr w5, [x0, #12]
ldr w6, [x0, #16]
ldr w7, [x0, #20]
ldr w8, [x0, #24]
ldr w9, [x0, #28]
ldr w10, [x0, #32]
ldr w11, [x0, #36]
ldr w12, [x0, #40]
ldr w13, [x0, #44]
ldr w14, [x0, #48]
ldr w15, [x0, #52]
ldr w16, [x0, #56]
ldr w17, [x0, #60]
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
ldr w1, [x0, #0]
add w2, w2, w1
str w2, [x0, #0]
ldr w1, [x0, #4]
add w3, w3, w1
str w3, [x0, #4]
ldr w1, [x0, #8]
add w4, w4, w1
str w4, [x0, #8]
ldr w1, [x0, #12]
add w5, w5, w1
str w5, [x0, #12]
ldr w1, [x0, #16]
add w6, w6, w1
str w6, [x0, #16]
ldr w1, [x0, #20]
add w7, w7, w1
str w7, [x0, #20]
ldr w1, [x0, #24]
add w8, w8, w1
str w8, [x0, #24]
ldr w1, [x0, #28]
add w9, w9, w1
str w9, [x0, #28]
ldr w1, [x0, #32]
add w10, w10, w1
str w10, [x0, #32]
ldr w1, [x0, #36]
add w11, w11, w1
str w11, [x0, #36]
ldr w1, [x0, #40]
add w12, w12, w1
str w12, [x0, #40]
ldr w1, [x0, #44]
add w13, w13, w1
str w13, [x0, #44]
ldr w1, [x0, #48]
add w14, w14, w1
str w14, [x0, #48]
ldr w1, [x0, #52]
add w15, w15, w1
str w15, [x0, #52]
ldr w1, [x0, #56]
add w16, w16, w1
str w16, [x0, #56]
ldr w1, [x0, #60]
add w17, w17, w1
str w17, [x0, #60]
add x24, x21, #0
add x19, x19, #64
add x20, x20, #64
add x21, x21, #64
sub x23, x23, #1
cbnz x23, 20b
ldr x19, [x22, #64]
ldr x20, [x22, #72]
ldr x21, [x22, #80]
ldr x23, [x22, #88]
ldr x24, [x22, #96]
ldr x22, [x22, #104]
ret
.p2align 6
.globl trial_bm_fold_io
trial_bm_fold_io:
str x19, [x4, #64]
str x20, [x4, #72]
str x21, [x4, #80]
str x23, [x4, #88]
str x24, [x4, #96]
str x22, [x4, #104]
add x23, x1, #0
add x19, x0, #0
add x20, x2, #0
add x22, x4, #0
lsl x9, x1, #6
add x21, x2, x9
lsl x9, x1, #7
add x24, x0, x9
sub x24, x24, #64
20:
ldr q0, [x24, #0]
ldr q1, [x19, #0]
eor v0.16b, v0.16b, v1.16b
str q0, [x20, #0]
ldr q0, [x24, #16]
ldr q1, [x19, #16]
eor v0.16b, v0.16b, v1.16b
str q0, [x20, #16]
ldr q0, [x24, #32]
ldr q1, [x19, #32]
eor v0.16b, v0.16b, v1.16b
str q0, [x20, #32]
ldr q0, [x24, #48]
ldr q1, [x19, #48]
eor v0.16b, v0.16b, v1.16b
str q0, [x20, #48]
add x0, x20, #0
ldr q4, [x0, #0]
ldr q5, [x0, #16]
ldr q6, [x0, #32]
ldr q7, [x0, #48]
umov x2, v4.d[0]
lsr x3, x2, #32
umov x4, v4.d[1]
lsr x5, x4, #32
umov x6, v5.d[0]
lsr x7, x6, #32
umov x8, v5.d[1]
lsr x9, x8, #32
umov x10, v6.d[0]
lsr x11, x10, #32
umov x12, v6.d[1]
lsr x13, x12, #32
umov x14, v7.d[0]
lsr x15, x14, #32
umov x16, v7.d[1]
lsr x17, x16, #32
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
lsl x1, x3, #32
orr x1, x1, x2
mov v0.d[0], x1
lsl x1, x5, #32
orr x1, x1, x4
mov v0.d[1], x1
lsl x1, x7, #32
orr x1, x1, x6
mov v1.d[0], x1
lsl x1, x9, #32
orr x1, x1, x8
mov v1.d[1], x1
lsl x1, x11, #32
orr x1, x1, x10
mov v2.d[0], x1
lsl x1, x13, #32
orr x1, x1, x12
mov v2.d[1], x1
lsl x1, x15, #32
orr x1, x1, x14
mov v3.d[0], x1
lsl x1, x17, #32
orr x1, x1, x16
mov v3.d[1], x1
add v0.4s, v0.4s, v4.4s
add v1.4s, v1.4s, v5.4s
add v2.4s, v2.4s, v6.4s
add v3.4s, v3.4s, v7.4s
str q0, [x0, #0]
str q1, [x0, #16]
str q2, [x0, #32]
str q3, [x0, #48]
add x19, x19, #64
ldr q0, [x20, #0]
ldr q1, [x19, #0]
eor v0.16b, v0.16b, v1.16b
str q0, [x21, #0]
ldr q0, [x20, #16]
ldr q1, [x19, #16]
eor v0.16b, v0.16b, v1.16b
str q0, [x21, #16]
ldr q0, [x20, #32]
ldr q1, [x19, #32]
eor v0.16b, v0.16b, v1.16b
str q0, [x21, #32]
ldr q0, [x20, #48]
ldr q1, [x19, #48]
eor v0.16b, v0.16b, v1.16b
str q0, [x21, #48]
add x0, x21, #0
ldr q4, [x0, #0]
ldr q5, [x0, #16]
ldr q6, [x0, #32]
ldr q7, [x0, #48]
umov x2, v4.d[0]
lsr x3, x2, #32
umov x4, v4.d[1]
lsr x5, x4, #32
umov x6, v5.d[0]
lsr x7, x6, #32
umov x8, v5.d[1]
lsr x9, x8, #32
umov x10, v6.d[0]
lsr x11, x10, #32
umov x12, v6.d[1]
lsr x13, x12, #32
umov x14, v7.d[0]
lsr x15, x14, #32
umov x16, v7.d[1]
lsr x17, x16, #32
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
add w1, w2, w14
eor w6, w6, w1, ror #25
add w1, w6, w2
eor w10, w10, w1, ror #23
add w1, w10, w6
eor w14, w14, w1, ror #19
add w1, w14, w10
eor w2, w2, w1, ror #14
add w1, w7, w3
eor w11, w11, w1, ror #25
add w1, w11, w7
eor w15, w15, w1, ror #23
add w1, w15, w11
eor w3, w3, w1, ror #19
add w1, w3, w15
eor w7, w7, w1, ror #14
add w1, w12, w8
eor w16, w16, w1, ror #25
add w1, w16, w12
eor w4, w4, w1, ror #23
add w1, w4, w16
eor w8, w8, w1, ror #19
add w1, w8, w4
eor w12, w12, w1, ror #14
add w1, w17, w13
eor w5, w5, w1, ror #25
add w1, w5, w17
eor w9, w9, w1, ror #23
add w1, w9, w5
eor w13, w13, w1, ror #19
add w1, w13, w9
eor w17, w17, w1, ror #14
add w1, w2, w5
eor w3, w3, w1, ror #25
add w1, w3, w2
eor w4, w4, w1, ror #23
add w1, w4, w3
eor w5, w5, w1, ror #19
add w1, w5, w4
eor w2, w2, w1, ror #14
add w1, w7, w6
eor w8, w8, w1, ror #25
add w1, w8, w7
eor w9, w9, w1, ror #23
add w1, w9, w8
eor w6, w6, w1, ror #19
add w1, w6, w9
eor w7, w7, w1, ror #14
add w1, w12, w11
eor w13, w13, w1, ror #25
add w1, w13, w12
eor w10, w10, w1, ror #23
add w1, w10, w13
eor w11, w11, w1, ror #19
add w1, w11, w10
eor w12, w12, w1, ror #14
add w1, w17, w16
eor w14, w14, w1, ror #25
add w1, w14, w17
eor w15, w15, w1, ror #23
add w1, w15, w14
eor w16, w16, w1, ror #19
add w1, w16, w15
eor w17, w17, w1, ror #14
lsl x1, x3, #32
orr x1, x1, x2
mov v0.d[0], x1
lsl x1, x5, #32
orr x1, x1, x4
mov v0.d[1], x1
lsl x1, x7, #32
orr x1, x1, x6
mov v1.d[0], x1
lsl x1, x9, #32
orr x1, x1, x8
mov v1.d[1], x1
lsl x1, x11, #32
orr x1, x1, x10
mov v2.d[0], x1
lsl x1, x13, #32
orr x1, x1, x12
mov v2.d[1], x1
lsl x1, x15, #32
orr x1, x1, x14
mov v3.d[0], x1
lsl x1, x17, #32
orr x1, x1, x16
mov v3.d[1], x1
add v0.4s, v0.4s, v4.4s
add v1.4s, v1.4s, v5.4s
add v2.4s, v2.4s, v6.4s
add v3.4s, v3.4s, v7.4s
str q0, [x0, #0]
str q1, [x0, #16]
str q2, [x0, #32]
str q3, [x0, #48]
add x24, x21, #0
add x19, x19, #64
add x20, x20, #64
add x21, x21, #64
sub x23, x23, #1
cbnz x23, 20b
ldr x19, [x22, #64]
ldr x20, [x22, #72]
ldr x21, [x22, #80]
ldr x23, [x22, #88]
ldr x24, [x22, #96]
ldr x22, [x22, #104]
ret
.p2align 6
.globl trial_bm_schedule
trial_bm_schedule:
str x30, [sp, #-16]!
str x19, [x4, #64]
str x20, [x4, #72]
str x21, [x4, #80]
str x23, [x4, #88]
str x24, [x4, #96]
str x22, [x4, #104]
add x23, x1, #0
add x19, x0, #0
add x20, x2, #0
add x22, x4, #0
lsl x9, x1, #6
add x21, x2, x9
lsl x9, x1, #7
add x24, x0, x9
sub x24, x24, #64
20:
ldr x9, [x24, #0]
ldr x10, [x19, #0]
eor x9, x9, x10
str x9, [x20, #0]
ldr x9, [x24, #8]
ldr x10, [x19, #8]
eor x9, x9, x10
str x9, [x20, #8]
ldr x9, [x24, #16]
ldr x10, [x19, #16]
eor x9, x9, x10
str x9, [x20, #16]
ldr x9, [x24, #24]
ldr x10, [x19, #24]
eor x9, x9, x10
str x9, [x20, #24]
ldr x9, [x24, #32]
ldr x10, [x19, #32]
eor x9, x9, x10
str x9, [x20, #32]
ldr x9, [x24, #40]
ldr x10, [x19, #40]
eor x9, x9, x10
str x9, [x20, #40]
ldr x9, [x24, #48]
ldr x10, [x19, #48]
eor x9, x9, x10
str x9, [x20, #48]
ldr x9, [x24, #56]
ldr x10, [x19, #56]
eor x9, x9, x10
str x9, [x20, #56]
add x0, x20, #0
add x1, x22, #0
bl trial_schedule
add x19, x19, #64
ldr x9, [x20, #0]
ldr x10, [x19, #0]
eor x9, x9, x10
str x9, [x21, #0]
ldr x9, [x20, #8]
ldr x10, [x19, #8]
eor x9, x9, x10
str x9, [x21, #8]
ldr x9, [x20, #16]
ldr x10, [x19, #16]
eor x9, x9, x10
str x9, [x21, #16]
ldr x9, [x20, #24]
ldr x10, [x19, #24]
eor x9, x9, x10
str x9, [x21, #24]
ldr x9, [x20, #32]
ldr x10, [x19, #32]
eor x9, x9, x10
str x9, [x21, #32]
ldr x9, [x20, #40]
ldr x10, [x19, #40]
eor x9, x9, x10
str x9, [x21, #40]
ldr x9, [x20, #48]
ldr x10, [x19, #48]
eor x9, x9, x10
str x9, [x21, #48]
ldr x9, [x20, #56]
ldr x10, [x19, #56]
eor x9, x9, x10
str x9, [x21, #56]
add x0, x21, #0
add x1, x22, #0
bl trial_schedule
add x24, x21, #0
add x19, x19, #64
add x20, x20, #64
add x21, x21, #64
sub x23, x23, #1
cbnz x23, 20b
ldr x19, [x22, #64]
ldr x20, [x22, #72]
ldr x21, [x22, #80]
ldr x23, [x22, #88]
ldr x24, [x22, #96]
ldr x22, [x22, #104]
ldr x30, [sp], #16
ret
.p2align 6
.globl trial_bm_schedule_fold
trial_bm_schedule_fold:
str x30, [sp, #-16]!
str x19, [x4, #64]
str x20, [x4, #72]
str x21, [x4, #80]
str x23, [x4, #88]
str x24, [x4, #96]
str x22, [x4, #104]
add x23, x1, #0
add x19, x0, #0
add x20, x2, #0
add x22, x4, #0
lsl x9, x1, #6
add x21, x2, x9
lsl x9, x1, #7
add x24, x0, x9
sub x24, x24, #64
20:
ldr x9, [x24, #0]
ldr x10, [x19, #0]
eor x9, x9, x10
str x9, [x20, #0]
ldr x9, [x24, #8]
ldr x10, [x19, #8]
eor x9, x9, x10
str x9, [x20, #8]
ldr x9, [x24, #16]
ldr x10, [x19, #16]
eor x9, x9, x10
str x9, [x20, #16]
ldr x9, [x24, #24]
ldr x10, [x19, #24]
eor x9, x9, x10
str x9, [x20, #24]
ldr x9, [x24, #32]
ldr x10, [x19, #32]
eor x9, x9, x10
str x9, [x20, #32]
ldr x9, [x24, #40]
ldr x10, [x19, #40]
eor x9, x9, x10
str x9, [x20, #40]
ldr x9, [x24, #48]
ldr x10, [x19, #48]
eor x9, x9, x10
str x9, [x20, #48]
ldr x9, [x24, #56]
ldr x10, [x19, #56]
eor x9, x9, x10
str x9, [x20, #56]
add x0, x20, #0
add x1, x22, #0
bl trial_schedule_fold
add x19, x19, #64
ldr x9, [x20, #0]
ldr x10, [x19, #0]
eor x9, x9, x10
str x9, [x21, #0]
ldr x9, [x20, #8]
ldr x10, [x19, #8]
eor x9, x9, x10
str x9, [x21, #8]
ldr x9, [x20, #16]
ldr x10, [x19, #16]
eor x9, x9, x10
str x9, [x21, #16]
ldr x9, [x20, #24]
ldr x10, [x19, #24]
eor x9, x9, x10
str x9, [x21, #24]
ldr x9, [x20, #32]
ldr x10, [x19, #32]
eor x9, x9, x10
str x9, [x21, #32]
ldr x9, [x20, #40]
ldr x10, [x19, #40]
eor x9, x9, x10
str x9, [x21, #40]
ldr x9, [x20, #48]
ldr x10, [x19, #48]
eor x9, x9, x10
str x9, [x21, #48]
ldr x9, [x20, #56]
ldr x10, [x19, #56]
eor x9, x9, x10
str x9, [x21, #56]
add x0, x21, #0
add x1, x22, #0
bl trial_schedule_fold
add x24, x21, #0
add x19, x19, #64
add x20, x20, #64
add x21, x21, #64
sub x23, x23, #1
cbnz x23, 20b
ldr x19, [x22, #64]
ldr x20, [x22, #72]
ldr x21, [x22, #80]
ldr x23, [x22, #88]
ldr x24, [x22, #96]
ldr x22, [x22, #104]
ldr x30, [sp], #16
ret
.p2align 6
.globl trial_rm_scalar
trial_rm_scalar:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_scalar
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_scalar
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_neon
trial_rm_neon:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_neon
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_neon
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_neon_loop
trial_rm_neon_loop:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_neon_loop
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_neon_loop
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_fused
trial_rm_fused:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_fused
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_fused
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_fused_loop
trial_rm_fused_loop:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_fused_loop
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_fused_loop
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_mem
trial_rm_resident_mem:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_mem
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_mem
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_ins
trial_rm_resident_ins:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ins
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ins
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_dup
trial_rm_resident_dup:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_dup
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_dup
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_ref
trial_rm_resident_ref:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ref
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ref
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_fold
trial_rm_fold:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_fold
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_fold
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_fold_vcopy
trial_rm_fold_vcopy:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_fold_vcopy
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_fold_vcopy
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_fold_inline
trial_rm_fold_inline:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_fold_inline
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_fold_inline
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_fold_io
trial_rm_fold_io:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_fold_io
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_fold_io
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_schedule
trial_rm_schedule:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_schedule
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_schedule
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_schedule_fold
trial_rm_schedule_fold:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr x12, [x9, #0]
str x12, [x10, #0]
add x9, x9, #8
add x10, x10, #8
sub x11, x11, #1
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_schedule_fold
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr x13, [x9, #0]
ldr x14, [x10, #0]
eor x13, x13, x14
str x13, [x11, #0]
add x9, x9, #8
add x10, x10, #8
add x11, x11, #8
sub x12, x12, #1
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_schedule_fold
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_scalar_v1
trial_rm_scalar_v1:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
str q0, [x10, #0]
add x9, x9, #16
add x10, x10, #16
sub x11, x11, #2
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_scalar
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q4, [x10, #0]
eor v0.16b, v0.16b, v4.16b
str q0, [x11, #0]
add x9, x9, #16
add x10, x10, #16
add x11, x11, #16
sub x12, x12, #2
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_scalar
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_schedule_v1
trial_rm_schedule_v1:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
str q0, [x10, #0]
add x9, x9, #16
add x10, x10, #16
sub x11, x11, #2
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_schedule
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q4, [x10, #0]
eor v0.16b, v0.16b, v4.16b
str q0, [x11, #0]
add x9, x9, #16
add x10, x10, #16
add x11, x11, #16
sub x12, x12, #2
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_schedule
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_mem_v1
trial_rm_resident_mem_v1:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
str q0, [x10, #0]
add x9, x9, #16
add x10, x10, #16
sub x11, x11, #2
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_mem
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q4, [x10, #0]
eor v0.16b, v0.16b, v4.16b
str q0, [x11, #0]
add x9, x9, #16
add x10, x10, #16
add x11, x11, #16
sub x12, x12, #2
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_mem
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_ins_v1
trial_rm_resident_ins_v1:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
str q0, [x10, #0]
add x9, x9, #16
add x10, x10, #16
sub x11, x11, #2
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ins
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q4, [x10, #0]
eor v0.16b, v0.16b, v4.16b
str q0, [x11, #0]
add x9, x9, #16
add x10, x10, #16
add x11, x11, #16
sub x12, x12, #2
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ins
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_dup_v1
trial_rm_resident_dup_v1:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
str q0, [x10, #0]
add x9, x9, #16
add x10, x10, #16
sub x11, x11, #2
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_dup
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q4, [x10, #0]
eor v0.16b, v0.16b, v4.16b
str q0, [x11, #0]
add x9, x9, #16
add x10, x10, #16
add x11, x11, #16
sub x12, x12, #2
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_dup
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_ref_v1
trial_rm_resident_ref_v1:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
str q0, [x10, #0]
add x9, x9, #16
add x10, x10, #16
sub x11, x11, #2
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ref
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q4, [x10, #0]
eor v0.16b, v0.16b, v4.16b
str q0, [x11, #0]
add x9, x9, #16
add x10, x10, #16
add x11, x11, #16
sub x12, x12, #2
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ref
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_scalar_v2
trial_rm_scalar_v2:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
str q0, [x10, #0]
str q1, [x10, #16]
add x9, x9, #32
add x10, x10, #32
sub x11, x11, #4
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_scalar
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q4, [x10, #0]
ldr q5, [x10, #16]
eor v0.16b, v0.16b, v4.16b
eor v1.16b, v1.16b, v5.16b
str q0, [x11, #0]
str q1, [x11, #16]
add x9, x9, #32
add x10, x10, #32
add x11, x11, #32
sub x12, x12, #4
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_scalar
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_schedule_v2
trial_rm_schedule_v2:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
str q0, [x10, #0]
str q1, [x10, #16]
add x9, x9, #32
add x10, x10, #32
sub x11, x11, #4
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_schedule
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q4, [x10, #0]
ldr q5, [x10, #16]
eor v0.16b, v0.16b, v4.16b
eor v1.16b, v1.16b, v5.16b
str q0, [x11, #0]
str q1, [x11, #16]
add x9, x9, #32
add x10, x10, #32
add x11, x11, #32
sub x12, x12, #4
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_schedule
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_mem_v2
trial_rm_resident_mem_v2:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
str q0, [x10, #0]
str q1, [x10, #16]
add x9, x9, #32
add x10, x10, #32
sub x11, x11, #4
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_mem
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q4, [x10, #0]
ldr q5, [x10, #16]
eor v0.16b, v0.16b, v4.16b
eor v1.16b, v1.16b, v5.16b
str q0, [x11, #0]
str q1, [x11, #16]
add x9, x9, #32
add x10, x10, #32
add x11, x11, #32
sub x12, x12, #4
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_mem
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_ins_v2
trial_rm_resident_ins_v2:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
str q0, [x10, #0]
str q1, [x10, #16]
add x9, x9, #32
add x10, x10, #32
sub x11, x11, #4
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ins
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q4, [x10, #0]
ldr q5, [x10, #16]
eor v0.16b, v0.16b, v4.16b
eor v1.16b, v1.16b, v5.16b
str q0, [x11, #0]
str q1, [x11, #16]
add x9, x9, #32
add x10, x10, #32
add x11, x11, #32
sub x12, x12, #4
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ins
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_dup_v2
trial_rm_resident_dup_v2:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
str q0, [x10, #0]
str q1, [x10, #16]
add x9, x9, #32
add x10, x10, #32
sub x11, x11, #4
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_dup
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q4, [x10, #0]
ldr q5, [x10, #16]
eor v0.16b, v0.16b, v4.16b
eor v1.16b, v1.16b, v5.16b
str q0, [x11, #0]
str q1, [x11, #16]
add x9, x9, #32
add x10, x10, #32
add x11, x11, #32
sub x12, x12, #4
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_dup
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_ref_v2
trial_rm_resident_ref_v2:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
str q0, [x10, #0]
str q1, [x10, #16]
add x9, x9, #32
add x10, x10, #32
sub x11, x11, #4
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ref
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q4, [x10, #0]
ldr q5, [x10, #16]
eor v0.16b, v0.16b, v4.16b
eor v1.16b, v1.16b, v5.16b
str q0, [x11, #0]
str q1, [x11, #16]
add x9, x9, #32
add x10, x10, #32
add x11, x11, #32
sub x12, x12, #4
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ref
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_scalar_v4
trial_rm_scalar_v4:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q2, [x9, #32]
ldr q3, [x9, #48]
str q0, [x10, #0]
str q1, [x10, #16]
str q2, [x10, #32]
str q3, [x10, #48]
add x9, x9, #64
add x10, x10, #64
sub x11, x11, #8
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_scalar
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q2, [x9, #32]
ldr q3, [x9, #48]
ldr q4, [x10, #0]
ldr q5, [x10, #16]
ldr q6, [x10, #32]
ldr q7, [x10, #48]
eor v0.16b, v0.16b, v4.16b
eor v1.16b, v1.16b, v5.16b
eor v2.16b, v2.16b, v6.16b
eor v3.16b, v3.16b, v7.16b
str q0, [x11, #0]
str q1, [x11, #16]
str q2, [x11, #32]
str q3, [x11, #48]
add x9, x9, #64
add x10, x10, #64
add x11, x11, #64
sub x12, x12, #8
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_scalar
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_schedule_v4
trial_rm_schedule_v4:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q2, [x9, #32]
ldr q3, [x9, #48]
str q0, [x10, #0]
str q1, [x10, #16]
str q2, [x10, #32]
str q3, [x10, #48]
add x9, x9, #64
add x10, x10, #64
sub x11, x11, #8
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_schedule
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q2, [x9, #32]
ldr q3, [x9, #48]
ldr q4, [x10, #0]
ldr q5, [x10, #16]
ldr q6, [x10, #32]
ldr q7, [x10, #48]
eor v0.16b, v0.16b, v4.16b
eor v1.16b, v1.16b, v5.16b
eor v2.16b, v2.16b, v6.16b
eor v3.16b, v3.16b, v7.16b
str q0, [x11, #0]
str q1, [x11, #16]
str q2, [x11, #32]
str q3, [x11, #48]
add x9, x9, #64
add x10, x10, #64
add x11, x11, #64
sub x12, x12, #8
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_schedule
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_mem_v4
trial_rm_resident_mem_v4:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q2, [x9, #32]
ldr q3, [x9, #48]
str q0, [x10, #0]
str q1, [x10, #16]
str q2, [x10, #32]
str q3, [x10, #48]
add x9, x9, #64
add x10, x10, #64
sub x11, x11, #8
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_mem
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q2, [x9, #32]
ldr q3, [x9, #48]
ldr q4, [x10, #0]
ldr q5, [x10, #16]
ldr q6, [x10, #32]
ldr q7, [x10, #48]
eor v0.16b, v0.16b, v4.16b
eor v1.16b, v1.16b, v5.16b
eor v2.16b, v2.16b, v6.16b
eor v3.16b, v3.16b, v7.16b
str q0, [x11, #0]
str q1, [x11, #16]
str q2, [x11, #32]
str q3, [x11, #48]
add x9, x9, #64
add x10, x10, #64
add x11, x11, #64
sub x12, x12, #8
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_mem
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_ins_v4
trial_rm_resident_ins_v4:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q2, [x9, #32]
ldr q3, [x9, #48]
str q0, [x10, #0]
str q1, [x10, #16]
str q2, [x10, #32]
str q3, [x10, #48]
add x9, x9, #64
add x10, x10, #64
sub x11, x11, #8
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ins
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q2, [x9, #32]
ldr q3, [x9, #48]
ldr q4, [x10, #0]
ldr q5, [x10, #16]
ldr q6, [x10, #32]
ldr q7, [x10, #48]
eor v0.16b, v0.16b, v4.16b
eor v1.16b, v1.16b, v5.16b
eor v2.16b, v2.16b, v6.16b
eor v3.16b, v3.16b, v7.16b
str q0, [x11, #0]
str q1, [x11, #16]
str q2, [x11, #32]
str q3, [x11, #48]
add x9, x9, #64
add x10, x10, #64
add x11, x11, #64
sub x12, x12, #8
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ins
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_dup_v4
trial_rm_resident_dup_v4:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q2, [x9, #32]
ldr q3, [x9, #48]
str q0, [x10, #0]
str q1, [x10, #16]
str q2, [x10, #32]
str q3, [x10, #48]
add x9, x9, #64
add x10, x10, #64
sub x11, x11, #8
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_dup
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q2, [x9, #32]
ldr q3, [x9, #48]
ldr q4, [x10, #0]
ldr q5, [x10, #16]
ldr q6, [x10, #32]
ldr q7, [x10, #48]
eor v0.16b, v0.16b, v4.16b
eor v1.16b, v1.16b, v5.16b
eor v2.16b, v2.16b, v6.16b
eor v3.16b, v3.16b, v7.16b
str q0, [x11, #0]
str q1, [x11, #16]
str q2, [x11, #32]
str q3, [x11, #48]
add x9, x9, #64
add x10, x10, #64
add x11, x11, #64
sub x12, x12, #8
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_dup
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
.p2align 6
.globl trial_rm_resident_ref_v4
trial_rm_resident_ref_v4:
str x19, [x4, #128]
str x20, [x4, #136]
str x22, [x4, #144]
str x23, [x4, #152]
str x24, [x4, #160]
str x30, [x4, #168]
str x21, [x4, #176]
add x19, x0, #0
add x20, x2, #0
add x21, x4, #0
lsl x22, x1, #7
add x9, x1, #0
movz x10, #1, lsl #0
add x11, x3, x3
20:
add x9, x9, x9
add x10, x10, x10
sub x12, x9, x11
cbnz x12, 20b
lsr x10, x10, #1
str x10, [x21, #184]
add x23, x10, #0
add x24, x20, #0
21:
add x9, x19, #0
add x10, x24, #0
lsr x11, x22, #3
22:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q2, [x9, #32]
ldr q3, [x9, #48]
str q0, [x10, #0]
str q1, [x10, #16]
str q2, [x10, #32]
str q3, [x10, #48]
add x9, x9, #64
add x10, x10, #64
sub x11, x11, #8
cbnz x11, 22b
add x0, x24, #0
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ref
add x24, x24, x22
sub x23, x23, #1
cbnz x23, 21b
ldr x23, [x21, #184]
sub x24, x23, #1
23:
add x9, x19, x22
sub x9, x9, #64
ldr x9, [x9, #0]
and x9, x9, x24
madd x10, x9, x22, x20
add x9, x19, #0
add x11, x21, #192
lsr x12, x22, #3
24:
ldr q0, [x9, #0]
ldr q1, [x9, #16]
ldr q2, [x9, #32]
ldr q3, [x9, #48]
ldr q4, [x10, #0]
ldr q5, [x10, #16]
ldr q6, [x10, #32]
ldr q7, [x10, #48]
eor v0.16b, v0.16b, v4.16b
eor v1.16b, v1.16b, v5.16b
eor v2.16b, v2.16b, v6.16b
eor v3.16b, v3.16b, v7.16b
str q0, [x11, #0]
str q1, [x11, #16]
str q2, [x11, #32]
str q3, [x11, #48]
add x9, x9, #64
add x10, x10, #64
add x11, x11, #64
sub x12, x12, #8
cbnz x12, 24b
add x0, x21, #192
lsr x1, x22, #7
add x2, x19, #0
add x3, x1, #0
add x4, x21, #0
bl trial_bm_resident_ref
sub x23, x23, #1
cbnz x23, 23b
ldr x19, [x21, #128]
ldr x20, [x21, #136]
ldr x22, [x21, #144]
ldr x23, [x21, #152]
ldr x24, [x21, #160]
ldr x30, [x21, #168]
ldr x21, [x21, #176]
ret
