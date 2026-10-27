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
