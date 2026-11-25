.text
.globl cr_fwd_c2
.p2align 4
cr_fwd_c2:
adrp x2, cr_fwd_c2_t
add x2, x2, :lo12:cr_fwd_c2_t
ldr q0, [x2, #0]
ldr q1, [x2, #16]
ldr q16, [x0, #0]
ldr q17, [x0, #32]
ldr q18, [x0, #64]
ldr q19, [x0, #96]
ldr q20, [x0, #128]
ldr q21, [x0, #160]
ldr q22, [x0, #192]
ldr q23, [x0, #224]
ldr q24, [x0, #256]
ldr q25, [x0, #288]
ldr q26, [x0, #320]
ldr q27, [x0, #352]
ldr q28, [x0, #384]
ldr q29, [x0, #416]
ldr q30, [x0, #448]
ldr q31, [x0, #480]
sqrdmulh v2.8h, v24.8h, v0.h[3]
sqrdmulh v4.8h, v25.8h, v0.h[3]
mul v3.8h, v24.8h, v0.h[2]
mul v5.8h, v25.8h, v0.h[2]
mls v3.8h, v2.8h, v0.h[0]
mls v5.8h, v4.8h, v0.h[0]
sub v2.8h, v16.8h, v3.8h
sub v4.8h, v17.8h, v5.8h
add v16.8h, v16.8h, v3.8h
add v17.8h, v17.8h, v5.8h
sqrdmulh v6.8h, v26.8h, v0.h[3]
sqrdmulh v3.8h, v27.8h, v0.h[3]
mul v7.8h, v26.8h, v0.h[2]
mul v24.8h, v27.8h, v0.h[2]
mls v7.8h, v6.8h, v0.h[0]
mls v24.8h, v3.8h, v0.h[0]
sub v6.8h, v18.8h, v7.8h
sub v3.8h, v19.8h, v24.8h
add v18.8h, v18.8h, v7.8h
add v19.8h, v19.8h, v24.8h
sqrdmulh v5.8h, v28.8h, v0.h[3]
sqrdmulh v7.8h, v29.8h, v0.h[3]
mul v25.8h, v28.8h, v0.h[2]
mul v26.8h, v29.8h, v0.h[2]
mls v25.8h, v5.8h, v0.h[0]
mls v26.8h, v7.8h, v0.h[0]
sub v5.8h, v20.8h, v25.8h
sub v7.8h, v21.8h, v26.8h
add v20.8h, v20.8h, v25.8h
add v21.8h, v21.8h, v26.8h
sqrdmulh v24.8h, v30.8h, v0.h[3]
sqrdmulh v25.8h, v31.8h, v0.h[3]
mul v27.8h, v30.8h, v0.h[2]
mul v28.8h, v31.8h, v0.h[2]
mls v27.8h, v24.8h, v0.h[0]
mls v28.8h, v25.8h, v0.h[0]
sub v24.8h, v22.8h, v27.8h
sub v25.8h, v23.8h, v28.8h
add v22.8h, v22.8h, v27.8h
add v23.8h, v23.8h, v28.8h
sqrdmulh v26.8h, v20.8h, v0.h[5]
sqrdmulh v27.8h, v21.8h, v0.h[5]
mul v29.8h, v20.8h, v0.h[4]
mul v30.8h, v21.8h, v0.h[4]
mls v29.8h, v26.8h, v0.h[0]
mls v30.8h, v27.8h, v0.h[0]
sub v26.8h, v16.8h, v29.8h
sub v27.8h, v17.8h, v30.8h
add v16.8h, v16.8h, v29.8h
add v17.8h, v17.8h, v30.8h
sqrdmulh v28.8h, v22.8h, v0.h[5]
sqrdmulh v29.8h, v23.8h, v0.h[5]
mul v31.8h, v22.8h, v0.h[4]
mul v20.8h, v23.8h, v0.h[4]
mls v31.8h, v28.8h, v0.h[0]
mls v20.8h, v29.8h, v0.h[0]
sub v28.8h, v18.8h, v31.8h
sub v29.8h, v19.8h, v20.8h
add v18.8h, v18.8h, v31.8h
add v19.8h, v19.8h, v20.8h
sqrdmulh v30.8h, v5.8h, v0.h[7]
sqrdmulh v31.8h, v7.8h, v0.h[7]
mul v21.8h, v5.8h, v0.h[6]
mul v22.8h, v7.8h, v0.h[6]
mls v21.8h, v30.8h, v0.h[0]
mls v22.8h, v31.8h, v0.h[0]
sub v30.8h, v2.8h, v21.8h
sub v31.8h, v4.8h, v22.8h
add v2.8h, v2.8h, v21.8h
add v4.8h, v4.8h, v22.8h
sqrdmulh v20.8h, v24.8h, v0.h[7]
sqrdmulh v21.8h, v25.8h, v0.h[7]
mul v23.8h, v24.8h, v0.h[6]
mul v5.8h, v25.8h, v0.h[6]
mls v23.8h, v20.8h, v0.h[0]
mls v5.8h, v21.8h, v0.h[0]
sub v20.8h, v6.8h, v23.8h
sub v21.8h, v3.8h, v5.8h
add v6.8h, v6.8h, v23.8h
add v3.8h, v3.8h, v5.8h
sqrdmulh v22.8h, v18.8h, v1.h[1]
sqrdmulh v23.8h, v19.8h, v1.h[1]
mul v7.8h, v18.8h, v1.h[0]
mul v24.8h, v19.8h, v1.h[0]
mls v7.8h, v22.8h, v0.h[0]
mls v24.8h, v23.8h, v0.h[0]
sub v22.8h, v16.8h, v7.8h
sub v23.8h, v17.8h, v24.8h
add v16.8h, v16.8h, v7.8h
add v17.8h, v17.8h, v24.8h
sqrdmulh v5.8h, v28.8h, v1.h[3]
sqrdmulh v7.8h, v29.8h, v1.h[3]
mul v25.8h, v28.8h, v1.h[2]
mul v18.8h, v29.8h, v1.h[2]
mls v25.8h, v5.8h, v0.h[0]
mls v18.8h, v7.8h, v0.h[0]
sub v5.8h, v26.8h, v25.8h
sub v7.8h, v27.8h, v18.8h
add v26.8h, v26.8h, v25.8h
add v27.8h, v27.8h, v18.8h
sqrdmulh v24.8h, v6.8h, v1.h[5]
sqrdmulh v25.8h, v3.8h, v1.h[5]
mul v19.8h, v6.8h, v1.h[4]
mul v28.8h, v3.8h, v1.h[4]
mls v19.8h, v24.8h, v0.h[0]
mls v28.8h, v25.8h, v0.h[0]
sub v24.8h, v2.8h, v19.8h
sub v25.8h, v4.8h, v28.8h
add v2.8h, v2.8h, v19.8h
add v4.8h, v4.8h, v28.8h
sqrdmulh v18.8h, v20.8h, v1.h[7]
sqrdmulh v19.8h, v21.8h, v1.h[7]
mul v29.8h, v20.8h, v1.h[6]
mul v6.8h, v21.8h, v1.h[6]
mls v29.8h, v18.8h, v0.h[0]
mls v6.8h, v19.8h, v0.h[0]
sub v18.8h, v30.8h, v29.8h
sub v19.8h, v31.8h, v6.8h
add v30.8h, v30.8h, v29.8h
add v31.8h, v31.8h, v6.8h
ldr q3, [x2, #32]
ldr q6, [x2, #48]
sqrdmulh v28.8h, v17.8h, v3.h[1]
sqrdmulh v20.8h, v23.8h, v3.h[3]
mul v29.8h, v17.8h, v3.h[0]
mul v21.8h, v23.8h, v3.h[2]
mls v29.8h, v28.8h, v0.h[0]
mls v21.8h, v20.8h, v0.h[0]
sub v28.8h, v16.8h, v29.8h
sub v20.8h, v22.8h, v21.8h
add v16.8h, v16.8h, v29.8h
add v22.8h, v22.8h, v21.8h
sqrdmulh v29.8h, v27.8h, v3.h[5]
sqrdmulh v21.8h, v7.8h, v3.h[7]
mul v17.8h, v27.8h, v3.h[4]
mul v23.8h, v7.8h, v3.h[6]
mls v17.8h, v29.8h, v0.h[0]
mls v23.8h, v21.8h, v0.h[0]
sub v29.8h, v26.8h, v17.8h
sub v21.8h, v5.8h, v23.8h
add v26.8h, v26.8h, v17.8h
add v5.8h, v5.8h, v23.8h
sqrdmulh v17.8h, v4.8h, v6.h[1]
sqrdmulh v23.8h, v25.8h, v6.h[3]
mul v27.8h, v4.8h, v6.h[0]
mul v7.8h, v25.8h, v6.h[2]
mls v27.8h, v17.8h, v0.h[0]
mls v7.8h, v23.8h, v0.h[0]
sub v17.8h, v2.8h, v27.8h
sub v23.8h, v24.8h, v7.8h
add v2.8h, v2.8h, v27.8h
add v24.8h, v24.8h, v7.8h
sqrdmulh v27.8h, v31.8h, v6.h[5]
sqrdmulh v7.8h, v19.8h, v6.h[7]
mul v4.8h, v31.8h, v6.h[4]
mul v25.8h, v19.8h, v6.h[6]
mls v4.8h, v27.8h, v0.h[0]
mls v25.8h, v7.8h, v0.h[0]
sub v27.8h, v30.8h, v4.8h
sub v7.8h, v18.8h, v25.8h
add v30.8h, v30.8h, v4.8h
add v18.8h, v18.8h, v25.8h
str q16, [x0, #0]
str q28, [x0, #32]
str q22, [x0, #64]
str q20, [x0, #96]
str q26, [x0, #128]
str q29, [x0, #160]
str q5, [x0, #192]
str q21, [x0, #224]
str q2, [x0, #256]
str q17, [x0, #288]
str q24, [x0, #320]
str q23, [x0, #352]
str q30, [x0, #384]
str q27, [x0, #416]
str q18, [x0, #448]
str q7, [x0, #480]
ldr q16, [x0, #16]
ldr q17, [x0, #48]
ldr q18, [x0, #80]
ldr q19, [x0, #112]
ldr q20, [x0, #144]
ldr q21, [x0, #176]
ldr q22, [x0, #208]
ldr q23, [x0, #240]
ldr q24, [x0, #272]
ldr q25, [x0, #304]
ldr q26, [x0, #336]
ldr q27, [x0, #368]
ldr q28, [x0, #400]
ldr q29, [x0, #432]
ldr q30, [x0, #464]
ldr q31, [x0, #496]
sqrdmulh v2.8h, v24.8h, v0.h[3]
sqrdmulh v4.8h, v25.8h, v0.h[3]
mul v3.8h, v24.8h, v0.h[2]
mul v5.8h, v25.8h, v0.h[2]
mls v3.8h, v2.8h, v0.h[0]
mls v5.8h, v4.8h, v0.h[0]
sub v2.8h, v16.8h, v3.8h
sub v4.8h, v17.8h, v5.8h
add v16.8h, v16.8h, v3.8h
add v17.8h, v17.8h, v5.8h
sqrdmulh v6.8h, v26.8h, v0.h[3]
sqrdmulh v3.8h, v27.8h, v0.h[3]
mul v7.8h, v26.8h, v0.h[2]
mul v24.8h, v27.8h, v0.h[2]
mls v7.8h, v6.8h, v0.h[0]
mls v24.8h, v3.8h, v0.h[0]
sub v6.8h, v18.8h, v7.8h
sub v3.8h, v19.8h, v24.8h
add v18.8h, v18.8h, v7.8h
add v19.8h, v19.8h, v24.8h
sqrdmulh v5.8h, v28.8h, v0.h[3]
sqrdmulh v7.8h, v29.8h, v0.h[3]
mul v25.8h, v28.8h, v0.h[2]
mul v26.8h, v29.8h, v0.h[2]
mls v25.8h, v5.8h, v0.h[0]
mls v26.8h, v7.8h, v0.h[0]
sub v5.8h, v20.8h, v25.8h
sub v7.8h, v21.8h, v26.8h
add v20.8h, v20.8h, v25.8h
add v21.8h, v21.8h, v26.8h
sqrdmulh v24.8h, v30.8h, v0.h[3]
sqrdmulh v25.8h, v31.8h, v0.h[3]
mul v27.8h, v30.8h, v0.h[2]
mul v28.8h, v31.8h, v0.h[2]
mls v27.8h, v24.8h, v0.h[0]
mls v28.8h, v25.8h, v0.h[0]
sub v24.8h, v22.8h, v27.8h
sub v25.8h, v23.8h, v28.8h
add v22.8h, v22.8h, v27.8h
add v23.8h, v23.8h, v28.8h
sqrdmulh v26.8h, v20.8h, v0.h[5]
sqrdmulh v27.8h, v21.8h, v0.h[5]
mul v29.8h, v20.8h, v0.h[4]
mul v30.8h, v21.8h, v0.h[4]
mls v29.8h, v26.8h, v0.h[0]
mls v30.8h, v27.8h, v0.h[0]
sub v26.8h, v16.8h, v29.8h
sub v27.8h, v17.8h, v30.8h
add v16.8h, v16.8h, v29.8h
add v17.8h, v17.8h, v30.8h
sqrdmulh v28.8h, v22.8h, v0.h[5]
sqrdmulh v29.8h, v23.8h, v0.h[5]
mul v31.8h, v22.8h, v0.h[4]
mul v20.8h, v23.8h, v0.h[4]
mls v31.8h, v28.8h, v0.h[0]
mls v20.8h, v29.8h, v0.h[0]
sub v28.8h, v18.8h, v31.8h
sub v29.8h, v19.8h, v20.8h
add v18.8h, v18.8h, v31.8h
add v19.8h, v19.8h, v20.8h
sqrdmulh v30.8h, v5.8h, v0.h[7]
sqrdmulh v31.8h, v7.8h, v0.h[7]
mul v21.8h, v5.8h, v0.h[6]
mul v22.8h, v7.8h, v0.h[6]
mls v21.8h, v30.8h, v0.h[0]
mls v22.8h, v31.8h, v0.h[0]
sub v30.8h, v2.8h, v21.8h
sub v31.8h, v4.8h, v22.8h
add v2.8h, v2.8h, v21.8h
add v4.8h, v4.8h, v22.8h
sqrdmulh v20.8h, v24.8h, v0.h[7]
sqrdmulh v21.8h, v25.8h, v0.h[7]
mul v23.8h, v24.8h, v0.h[6]
mul v5.8h, v25.8h, v0.h[6]
mls v23.8h, v20.8h, v0.h[0]
mls v5.8h, v21.8h, v0.h[0]
sub v20.8h, v6.8h, v23.8h
sub v21.8h, v3.8h, v5.8h
add v6.8h, v6.8h, v23.8h
add v3.8h, v3.8h, v5.8h
sqrdmulh v22.8h, v18.8h, v1.h[1]
sqrdmulh v23.8h, v19.8h, v1.h[1]
mul v7.8h, v18.8h, v1.h[0]
mul v24.8h, v19.8h, v1.h[0]
mls v7.8h, v22.8h, v0.h[0]
mls v24.8h, v23.8h, v0.h[0]
sub v22.8h, v16.8h, v7.8h
sub v23.8h, v17.8h, v24.8h
add v16.8h, v16.8h, v7.8h
add v17.8h, v17.8h, v24.8h
sqrdmulh v5.8h, v28.8h, v1.h[3]
sqrdmulh v7.8h, v29.8h, v1.h[3]
mul v25.8h, v28.8h, v1.h[2]
mul v18.8h, v29.8h, v1.h[2]
mls v25.8h, v5.8h, v0.h[0]
mls v18.8h, v7.8h, v0.h[0]
sub v5.8h, v26.8h, v25.8h
sub v7.8h, v27.8h, v18.8h
add v26.8h, v26.8h, v25.8h
add v27.8h, v27.8h, v18.8h
sqrdmulh v24.8h, v6.8h, v1.h[5]
sqrdmulh v25.8h, v3.8h, v1.h[5]
mul v19.8h, v6.8h, v1.h[4]
mul v28.8h, v3.8h, v1.h[4]
mls v19.8h, v24.8h, v0.h[0]
mls v28.8h, v25.8h, v0.h[0]
sub v24.8h, v2.8h, v19.8h
sub v25.8h, v4.8h, v28.8h
add v2.8h, v2.8h, v19.8h
add v4.8h, v4.8h, v28.8h
sqrdmulh v18.8h, v20.8h, v1.h[7]
sqrdmulh v19.8h, v21.8h, v1.h[7]
mul v29.8h, v20.8h, v1.h[6]
mul v6.8h, v21.8h, v1.h[6]
mls v29.8h, v18.8h, v0.h[0]
mls v6.8h, v19.8h, v0.h[0]
sub v18.8h, v30.8h, v29.8h
sub v19.8h, v31.8h, v6.8h
add v30.8h, v30.8h, v29.8h
add v31.8h, v31.8h, v6.8h
ldr q3, [x2, #32]
ldr q6, [x2, #48]
sqrdmulh v28.8h, v17.8h, v3.h[1]
sqrdmulh v20.8h, v23.8h, v3.h[3]
mul v29.8h, v17.8h, v3.h[0]
mul v21.8h, v23.8h, v3.h[2]
mls v29.8h, v28.8h, v0.h[0]
mls v21.8h, v20.8h, v0.h[0]
sub v28.8h, v16.8h, v29.8h
sub v20.8h, v22.8h, v21.8h
add v16.8h, v16.8h, v29.8h
add v22.8h, v22.8h, v21.8h
sqrdmulh v29.8h, v27.8h, v3.h[5]
sqrdmulh v21.8h, v7.8h, v3.h[7]
mul v17.8h, v27.8h, v3.h[4]
mul v23.8h, v7.8h, v3.h[6]
mls v17.8h, v29.8h, v0.h[0]
mls v23.8h, v21.8h, v0.h[0]
sub v29.8h, v26.8h, v17.8h
sub v21.8h, v5.8h, v23.8h
add v26.8h, v26.8h, v17.8h
add v5.8h, v5.8h, v23.8h
sqrdmulh v17.8h, v4.8h, v6.h[1]
sqrdmulh v23.8h, v25.8h, v6.h[3]
mul v27.8h, v4.8h, v6.h[0]
mul v7.8h, v25.8h, v6.h[2]
mls v27.8h, v17.8h, v0.h[0]
mls v7.8h, v23.8h, v0.h[0]
sub v17.8h, v2.8h, v27.8h
sub v23.8h, v24.8h, v7.8h
add v2.8h, v2.8h, v27.8h
add v24.8h, v24.8h, v7.8h
sqrdmulh v27.8h, v31.8h, v6.h[5]
sqrdmulh v7.8h, v19.8h, v6.h[7]
mul v4.8h, v31.8h, v6.h[4]
mul v25.8h, v19.8h, v6.h[6]
mls v4.8h, v27.8h, v0.h[0]
mls v25.8h, v7.8h, v0.h[0]
sub v27.8h, v30.8h, v4.8h
sub v7.8h, v18.8h, v25.8h
add v30.8h, v30.8h, v4.8h
add v18.8h, v18.8h, v25.8h
str q16, [x0, #16]
str q28, [x0, #48]
str q22, [x0, #80]
str q20, [x0, #112]
str q26, [x0, #144]
str q29, [x0, #176]
str q5, [x0, #208]
str q21, [x0, #240]
str q2, [x0, #272]
str q17, [x0, #304]
str q24, [x0, #336]
str q23, [x0, #368]
str q30, [x0, #400]
str q27, [x0, #432]
str q18, [x0, #464]
str q7, [x0, #496]
ldr q1, [x2, #64]
ldr q2, [x2, #80]
ldr q3, [x2, #96]
ldr q4, [x2, #112]
ldr q16, [x0, #0]
ldr q17, [x0, #16]
sqrdmulh v18.8h, v17.8h, v1.h[1]
mul v19.8h, v17.8h, v1.h[0]
mls v19.8h, v18.8h, v0.h[0]
sub v17.8h, v16.8h, v19.8h
add v16.8h, v16.8h, v19.8h
trn1 v18.2d, v16.2d, v17.2d
trn2 v19.2d, v16.2d, v17.2d
ldr q16, [x2, #144]
ldr q17, [x2, #128]
sqrdmulh v16.8h, v19.8h, v16.8h
mul v17.8h, v19.8h, v17.8h
mls v17.8h, v16.8h, v0.h[0]
sub v19.8h, v18.8h, v17.8h
add v18.8h, v18.8h, v17.8h
ldr q20, [x0, #32]
trn1 v16.4s, v18.4s, v19.4s
ldr q21, [x0, #48]
trn2 v17.4s, v18.4s, v19.4s
sqrdmulh v22.8h, v21.8h, v1.h[3]
ldr q18, [x2, #176]
mul v23.8h, v21.8h, v1.h[2]
ldr q19, [x2, #160]
mls v23.8h, v22.8h, v0.h[0]
sqrdmulh v18.8h, v17.8h, v18.8h
sub v21.8h, v20.8h, v23.8h
mul v19.8h, v17.8h, v19.8h
add v20.8h, v20.8h, v23.8h
mls v19.8h, v18.8h, v0.h[0]
trn1 v22.2d, v20.2d, v21.2d
sub v17.8h, v16.8h, v19.8h
trn2 v23.2d, v20.2d, v21.2d
add v16.8h, v16.8h, v19.8h
ldr q20, [x2, #208]
sqrdmulh v18.8h, v16.8h, v0.h[1]
ldr q21, [x2, #192]
sqrdmulh v19.8h, v17.8h, v0.h[1]
sqrdmulh v20.8h, v23.8h, v20.8h
sshr v18.8h, v18.8h, #11
mul v21.8h, v23.8h, v21.8h
sshr v19.8h, v19.8h, #11
mls v21.8h, v20.8h, v0.h[0]
mls v16.8h, v18.8h, v0.h[0]
sub v23.8h, v22.8h, v21.8h
mls v17.8h, v19.8h, v0.h[0]
add v22.8h, v22.8h, v21.8h
ldr q24, [x0, #64]
zip1 v18.4s, v16.4s, v17.4s
trn1 v20.4s, v22.4s, v23.4s
ldr q25, [x0, #80]
zip2 v19.4s, v16.4s, v17.4s
trn2 v21.4s, v22.4s, v23.4s
sqrdmulh v26.8h, v25.8h, v1.h[5]
str q18, [x0, #0]
ldr q22, [x2, #240]
mul v27.8h, v25.8h, v1.h[4]
str q19, [x0, #16]
ldr q23, [x2, #224]
mls v27.8h, v26.8h, v0.h[0]
sqrdmulh v22.8h, v21.8h, v22.8h
sub v25.8h, v24.8h, v27.8h
mul v23.8h, v21.8h, v23.8h
add v24.8h, v24.8h, v27.8h
mls v23.8h, v22.8h, v0.h[0]
trn1 v26.2d, v24.2d, v25.2d
sub v21.8h, v20.8h, v23.8h
trn2 v27.2d, v24.2d, v25.2d
add v20.8h, v20.8h, v23.8h
ldr q24, [x2, #272]
sqrdmulh v22.8h, v20.8h, v0.h[1]
ldr q25, [x2, #256]
sqrdmulh v23.8h, v21.8h, v0.h[1]
sqrdmulh v24.8h, v27.8h, v24.8h
sshr v22.8h, v22.8h, #11
mul v25.8h, v27.8h, v25.8h
sshr v23.8h, v23.8h, #11
mls v25.8h, v24.8h, v0.h[0]
mls v20.8h, v22.8h, v0.h[0]
sub v27.8h, v26.8h, v25.8h
mls v21.8h, v23.8h, v0.h[0]
add v26.8h, v26.8h, v25.8h
ldr q28, [x0, #96]
zip1 v22.4s, v20.4s, v21.4s
trn1 v24.4s, v26.4s, v27.4s
ldr q29, [x0, #112]
zip2 v23.4s, v20.4s, v21.4s
trn2 v25.4s, v26.4s, v27.4s
sqrdmulh v30.8h, v29.8h, v1.h[7]
str q22, [x0, #32]
ldr q26, [x2, #304]
mul v31.8h, v29.8h, v1.h[6]
str q23, [x0, #48]
ldr q27, [x2, #288]
mls v31.8h, v30.8h, v0.h[0]
sqrdmulh v26.8h, v25.8h, v26.8h
sub v29.8h, v28.8h, v31.8h
mul v27.8h, v25.8h, v27.8h
add v28.8h, v28.8h, v31.8h
mls v27.8h, v26.8h, v0.h[0]
trn1 v30.2d, v28.2d, v29.2d
sub v25.8h, v24.8h, v27.8h
trn2 v31.2d, v28.2d, v29.2d
add v24.8h, v24.8h, v27.8h
ldr q28, [x2, #336]
sqrdmulh v26.8h, v24.8h, v0.h[1]
ldr q29, [x2, #320]
sqrdmulh v27.8h, v25.8h, v0.h[1]
sqrdmulh v28.8h, v31.8h, v28.8h
sshr v26.8h, v26.8h, #11
mul v29.8h, v31.8h, v29.8h
sshr v27.8h, v27.8h, #11
mls v29.8h, v28.8h, v0.h[0]
mls v24.8h, v26.8h, v0.h[0]
sub v31.8h, v30.8h, v29.8h
mls v25.8h, v27.8h, v0.h[0]
add v30.8h, v30.8h, v29.8h
ldr q5, [x0, #128]
zip1 v26.4s, v24.4s, v25.4s
trn1 v28.4s, v30.4s, v31.4s
ldr q6, [x0, #144]
zip2 v27.4s, v24.4s, v25.4s
trn2 v29.4s, v30.4s, v31.4s
sqrdmulh v7.8h, v6.8h, v2.h[1]
str q26, [x0, #64]
ldr q30, [x2, #368]
mul v16.8h, v6.8h, v2.h[0]
str q27, [x0, #80]
ldr q31, [x2, #352]
mls v16.8h, v7.8h, v0.h[0]
sqrdmulh v30.8h, v29.8h, v30.8h
sub v6.8h, v5.8h, v16.8h
mul v31.8h, v29.8h, v31.8h
add v5.8h, v5.8h, v16.8h
mls v31.8h, v30.8h, v0.h[0]
trn1 v7.2d, v5.2d, v6.2d
sub v29.8h, v28.8h, v31.8h
trn2 v16.2d, v5.2d, v6.2d
add v28.8h, v28.8h, v31.8h
ldr q5, [x2, #400]
sqrdmulh v30.8h, v28.8h, v0.h[1]
ldr q6, [x2, #384]
sqrdmulh v31.8h, v29.8h, v0.h[1]
sqrdmulh v5.8h, v16.8h, v5.8h
sshr v30.8h, v30.8h, #11
mul v6.8h, v16.8h, v6.8h
sshr v31.8h, v31.8h, #11
mls v6.8h, v5.8h, v0.h[0]
mls v28.8h, v30.8h, v0.h[0]
sub v16.8h, v7.8h, v6.8h
mls v29.8h, v31.8h, v0.h[0]
add v7.8h, v7.8h, v6.8h
ldr q17, [x0, #160]
zip1 v30.4s, v28.4s, v29.4s
trn1 v5.4s, v7.4s, v16.4s
ldr q18, [x0, #176]
zip2 v31.4s, v28.4s, v29.4s
trn2 v6.4s, v7.4s, v16.4s
sqrdmulh v19.8h, v18.8h, v2.h[3]
str q30, [x0, #96]
ldr q7, [x2, #432]
mul v20.8h, v18.8h, v2.h[2]
str q31, [x0, #112]
ldr q16, [x2, #416]
mls v20.8h, v19.8h, v0.h[0]
sqrdmulh v7.8h, v6.8h, v7.8h
sub v18.8h, v17.8h, v20.8h
mul v16.8h, v6.8h, v16.8h
add v17.8h, v17.8h, v20.8h
mls v16.8h, v7.8h, v0.h[0]
trn1 v19.2d, v17.2d, v18.2d
sub v6.8h, v5.8h, v16.8h
trn2 v20.2d, v17.2d, v18.2d
add v5.8h, v5.8h, v16.8h
ldr q17, [x2, #464]
sqrdmulh v7.8h, v5.8h, v0.h[1]
ldr q18, [x2, #448]
sqrdmulh v16.8h, v6.8h, v0.h[1]
sqrdmulh v17.8h, v20.8h, v17.8h
sshr v7.8h, v7.8h, #11
mul v18.8h, v20.8h, v18.8h
sshr v16.8h, v16.8h, #11
mls v18.8h, v17.8h, v0.h[0]
mls v5.8h, v7.8h, v0.h[0]
sub v20.8h, v19.8h, v18.8h
mls v6.8h, v16.8h, v0.h[0]
add v19.8h, v19.8h, v18.8h
ldr q21, [x0, #192]
zip1 v7.4s, v5.4s, v6.4s
trn1 v17.4s, v19.4s, v20.4s
ldr q22, [x0, #208]
zip2 v16.4s, v5.4s, v6.4s
trn2 v18.4s, v19.4s, v20.4s
sqrdmulh v23.8h, v22.8h, v2.h[5]
str q7, [x0, #128]
ldr q19, [x2, #496]
mul v24.8h, v22.8h, v2.h[4]
str q16, [x0, #144]
ldr q20, [x2, #480]
mls v24.8h, v23.8h, v0.h[0]
sqrdmulh v19.8h, v18.8h, v19.8h
sub v22.8h, v21.8h, v24.8h
mul v20.8h, v18.8h, v20.8h
add v21.8h, v21.8h, v24.8h
mls v20.8h, v19.8h, v0.h[0]
trn1 v23.2d, v21.2d, v22.2d
sub v18.8h, v17.8h, v20.8h
trn2 v24.2d, v21.2d, v22.2d
add v17.8h, v17.8h, v20.8h
ldr q21, [x2, #528]
sqrdmulh v19.8h, v17.8h, v0.h[1]
ldr q22, [x2, #512]
sqrdmulh v20.8h, v18.8h, v0.h[1]
sqrdmulh v21.8h, v24.8h, v21.8h
sshr v19.8h, v19.8h, #11
mul v22.8h, v24.8h, v22.8h
sshr v20.8h, v20.8h, #11
mls v22.8h, v21.8h, v0.h[0]
mls v17.8h, v19.8h, v0.h[0]
sub v24.8h, v23.8h, v22.8h
mls v18.8h, v20.8h, v0.h[0]
add v23.8h, v23.8h, v22.8h
ldr q25, [x0, #224]
zip1 v19.4s, v17.4s, v18.4s
trn1 v21.4s, v23.4s, v24.4s
ldr q26, [x0, #240]
zip2 v20.4s, v17.4s, v18.4s
trn2 v22.4s, v23.4s, v24.4s
sqrdmulh v27.8h, v26.8h, v2.h[7]
str q19, [x0, #160]
ldr q23, [x2, #560]
mul v28.8h, v26.8h, v2.h[6]
str q20, [x0, #176]
ldr q24, [x2, #544]
mls v28.8h, v27.8h, v0.h[0]
sqrdmulh v23.8h, v22.8h, v23.8h
sub v26.8h, v25.8h, v28.8h
mul v24.8h, v22.8h, v24.8h
add v25.8h, v25.8h, v28.8h
mls v24.8h, v23.8h, v0.h[0]
trn1 v27.2d, v25.2d, v26.2d
sub v22.8h, v21.8h, v24.8h
trn2 v28.2d, v25.2d, v26.2d
add v21.8h, v21.8h, v24.8h
ldr q25, [x2, #592]
sqrdmulh v23.8h, v21.8h, v0.h[1]
ldr q26, [x2, #576]
sqrdmulh v24.8h, v22.8h, v0.h[1]
sqrdmulh v25.8h, v28.8h, v25.8h
sshr v23.8h, v23.8h, #11
mul v26.8h, v28.8h, v26.8h
sshr v24.8h, v24.8h, #11
mls v26.8h, v25.8h, v0.h[0]
mls v21.8h, v23.8h, v0.h[0]
sub v28.8h, v27.8h, v26.8h
mls v22.8h, v24.8h, v0.h[0]
add v27.8h, v27.8h, v26.8h
ldr q29, [x0, #256]
zip1 v23.4s, v21.4s, v22.4s
trn1 v25.4s, v27.4s, v28.4s
ldr q30, [x0, #272]
zip2 v24.4s, v21.4s, v22.4s
trn2 v26.4s, v27.4s, v28.4s
sqrdmulh v31.8h, v30.8h, v3.h[1]
str q23, [x0, #192]
ldr q27, [x2, #624]
mul v5.8h, v30.8h, v3.h[0]
str q24, [x0, #208]
ldr q28, [x2, #608]
mls v5.8h, v31.8h, v0.h[0]
sqrdmulh v27.8h, v26.8h, v27.8h
sub v30.8h, v29.8h, v5.8h
mul v28.8h, v26.8h, v28.8h
add v29.8h, v29.8h, v5.8h
mls v28.8h, v27.8h, v0.h[0]
trn1 v31.2d, v29.2d, v30.2d
sub v26.8h, v25.8h, v28.8h
trn2 v5.2d, v29.2d, v30.2d
add v25.8h, v25.8h, v28.8h
ldr q29, [x2, #656]
sqrdmulh v27.8h, v25.8h, v0.h[1]
ldr q30, [x2, #640]
sqrdmulh v28.8h, v26.8h, v0.h[1]
sqrdmulh v29.8h, v5.8h, v29.8h
sshr v27.8h, v27.8h, #11
mul v30.8h, v5.8h, v30.8h
sshr v28.8h, v28.8h, #11
mls v30.8h, v29.8h, v0.h[0]
mls v25.8h, v27.8h, v0.h[0]
sub v5.8h, v31.8h, v30.8h
mls v26.8h, v28.8h, v0.h[0]
add v31.8h, v31.8h, v30.8h
ldr q6, [x0, #288]
zip1 v27.4s, v25.4s, v26.4s
trn1 v29.4s, v31.4s, v5.4s
ldr q7, [x0, #304]
zip2 v28.4s, v25.4s, v26.4s
trn2 v30.4s, v31.4s, v5.4s
sqrdmulh v16.8h, v7.8h, v3.h[3]
str q27, [x0, #224]
ldr q31, [x2, #688]
mul v17.8h, v7.8h, v3.h[2]
str q28, [x0, #240]
ldr q5, [x2, #672]
mls v17.8h, v16.8h, v0.h[0]
sqrdmulh v31.8h, v30.8h, v31.8h
sub v7.8h, v6.8h, v17.8h
mul v5.8h, v30.8h, v5.8h
add v6.8h, v6.8h, v17.8h
mls v5.8h, v31.8h, v0.h[0]
trn1 v16.2d, v6.2d, v7.2d
sub v30.8h, v29.8h, v5.8h
trn2 v17.2d, v6.2d, v7.2d
add v29.8h, v29.8h, v5.8h
ldr q6, [x2, #720]
sqrdmulh v31.8h, v29.8h, v0.h[1]
ldr q7, [x2, #704]
sqrdmulh v5.8h, v30.8h, v0.h[1]
sqrdmulh v6.8h, v17.8h, v6.8h
sshr v31.8h, v31.8h, #11
mul v7.8h, v17.8h, v7.8h
sshr v5.8h, v5.8h, #11
mls v7.8h, v6.8h, v0.h[0]
mls v29.8h, v31.8h, v0.h[0]
sub v17.8h, v16.8h, v7.8h
mls v30.8h, v5.8h, v0.h[0]
add v16.8h, v16.8h, v7.8h
ldr q18, [x0, #320]
zip1 v31.4s, v29.4s, v30.4s
trn1 v6.4s, v16.4s, v17.4s
ldr q19, [x0, #336]
zip2 v5.4s, v29.4s, v30.4s
trn2 v7.4s, v16.4s, v17.4s
sqrdmulh v20.8h, v19.8h, v3.h[5]
str q31, [x0, #256]
ldr q16, [x2, #752]
mul v21.8h, v19.8h, v3.h[4]
str q5, [x0, #272]
ldr q17, [x2, #736]
mls v21.8h, v20.8h, v0.h[0]
sqrdmulh v16.8h, v7.8h, v16.8h
sub v19.8h, v18.8h, v21.8h
mul v17.8h, v7.8h, v17.8h
add v18.8h, v18.8h, v21.8h
mls v17.8h, v16.8h, v0.h[0]
trn1 v20.2d, v18.2d, v19.2d
sub v7.8h, v6.8h, v17.8h
trn2 v21.2d, v18.2d, v19.2d
add v6.8h, v6.8h, v17.8h
ldr q18, [x2, #784]
sqrdmulh v16.8h, v6.8h, v0.h[1]
ldr q19, [x2, #768]
sqrdmulh v17.8h, v7.8h, v0.h[1]
sqrdmulh v18.8h, v21.8h, v18.8h
sshr v16.8h, v16.8h, #11
mul v19.8h, v21.8h, v19.8h
sshr v17.8h, v17.8h, #11
mls v19.8h, v18.8h, v0.h[0]
mls v6.8h, v16.8h, v0.h[0]
sub v21.8h, v20.8h, v19.8h
mls v7.8h, v17.8h, v0.h[0]
add v20.8h, v20.8h, v19.8h
ldr q22, [x0, #352]
zip1 v16.4s, v6.4s, v7.4s
trn1 v18.4s, v20.4s, v21.4s
ldr q23, [x0, #368]
zip2 v17.4s, v6.4s, v7.4s
trn2 v19.4s, v20.4s, v21.4s
sqrdmulh v24.8h, v23.8h, v3.h[7]
str q16, [x0, #288]
ldr q20, [x2, #816]
mul v25.8h, v23.8h, v3.h[6]
str q17, [x0, #304]
ldr q21, [x2, #800]
mls v25.8h, v24.8h, v0.h[0]
sqrdmulh v20.8h, v19.8h, v20.8h
sub v23.8h, v22.8h, v25.8h
mul v21.8h, v19.8h, v21.8h
add v22.8h, v22.8h, v25.8h
mls v21.8h, v20.8h, v0.h[0]
trn1 v24.2d, v22.2d, v23.2d
sub v19.8h, v18.8h, v21.8h
trn2 v25.2d, v22.2d, v23.2d
add v18.8h, v18.8h, v21.8h
ldr q22, [x2, #848]
sqrdmulh v20.8h, v18.8h, v0.h[1]
ldr q23, [x2, #832]
sqrdmulh v21.8h, v19.8h, v0.h[1]
sqrdmulh v22.8h, v25.8h, v22.8h
sshr v20.8h, v20.8h, #11
mul v23.8h, v25.8h, v23.8h
sshr v21.8h, v21.8h, #11
mls v23.8h, v22.8h, v0.h[0]
mls v18.8h, v20.8h, v0.h[0]
sub v25.8h, v24.8h, v23.8h
mls v19.8h, v21.8h, v0.h[0]
add v24.8h, v24.8h, v23.8h
ldr q26, [x0, #384]
zip1 v20.4s, v18.4s, v19.4s
trn1 v22.4s, v24.4s, v25.4s
ldr q27, [x0, #400]
zip2 v21.4s, v18.4s, v19.4s
trn2 v23.4s, v24.4s, v25.4s
sqrdmulh v28.8h, v27.8h, v4.h[1]
str q20, [x0, #320]
ldr q24, [x2, #880]
mul v29.8h, v27.8h, v4.h[0]
str q21, [x0, #336]
ldr q25, [x2, #864]
mls v29.8h, v28.8h, v0.h[0]
sqrdmulh v24.8h, v23.8h, v24.8h
sub v27.8h, v26.8h, v29.8h
mul v25.8h, v23.8h, v25.8h
add v26.8h, v26.8h, v29.8h
mls v25.8h, v24.8h, v0.h[0]
trn1 v28.2d, v26.2d, v27.2d
sub v23.8h, v22.8h, v25.8h
trn2 v29.2d, v26.2d, v27.2d
add v22.8h, v22.8h, v25.8h
ldr q26, [x2, #912]
sqrdmulh v24.8h, v22.8h, v0.h[1]
ldr q27, [x2, #896]
sqrdmulh v25.8h, v23.8h, v0.h[1]
sqrdmulh v26.8h, v29.8h, v26.8h
sshr v24.8h, v24.8h, #11
mul v27.8h, v29.8h, v27.8h
sshr v25.8h, v25.8h, #11
mls v27.8h, v26.8h, v0.h[0]
mls v22.8h, v24.8h, v0.h[0]
sub v29.8h, v28.8h, v27.8h
mls v23.8h, v25.8h, v0.h[0]
add v28.8h, v28.8h, v27.8h
ldr q30, [x0, #416]
zip1 v24.4s, v22.4s, v23.4s
trn1 v26.4s, v28.4s, v29.4s
ldr q31, [x0, #432]
zip2 v25.4s, v22.4s, v23.4s
trn2 v27.4s, v28.4s, v29.4s
sqrdmulh v5.8h, v31.8h, v4.h[3]
str q24, [x0, #352]
ldr q28, [x2, #944]
mul v6.8h, v31.8h, v4.h[2]
str q25, [x0, #368]
ldr q29, [x2, #928]
mls v6.8h, v5.8h, v0.h[0]
sqrdmulh v28.8h, v27.8h, v28.8h
sub v31.8h, v30.8h, v6.8h
mul v29.8h, v27.8h, v29.8h
add v30.8h, v30.8h, v6.8h
mls v29.8h, v28.8h, v0.h[0]
trn1 v5.2d, v30.2d, v31.2d
sub v27.8h, v26.8h, v29.8h
trn2 v6.2d, v30.2d, v31.2d
add v26.8h, v26.8h, v29.8h
ldr q30, [x2, #976]
sqrdmulh v28.8h, v26.8h, v0.h[1]
ldr q31, [x2, #960]
sqrdmulh v29.8h, v27.8h, v0.h[1]
sqrdmulh v30.8h, v6.8h, v30.8h
sshr v28.8h, v28.8h, #11
mul v31.8h, v6.8h, v31.8h
sshr v29.8h, v29.8h, #11
mls v31.8h, v30.8h, v0.h[0]
mls v26.8h, v28.8h, v0.h[0]
sub v6.8h, v5.8h, v31.8h
mls v27.8h, v29.8h, v0.h[0]
add v5.8h, v5.8h, v31.8h
ldr q7, [x0, #448]
zip1 v28.4s, v26.4s, v27.4s
trn1 v30.4s, v5.4s, v6.4s
ldr q16, [x0, #464]
zip2 v29.4s, v26.4s, v27.4s
trn2 v31.4s, v5.4s, v6.4s
sqrdmulh v17.8h, v16.8h, v4.h[5]
str q28, [x0, #384]
ldr q5, [x2, #1008]
mul v18.8h, v16.8h, v4.h[4]
str q29, [x0, #400]
ldr q6, [x2, #992]
mls v18.8h, v17.8h, v0.h[0]
sqrdmulh v5.8h, v31.8h, v5.8h
sub v16.8h, v7.8h, v18.8h
mul v6.8h, v31.8h, v6.8h
add v7.8h, v7.8h, v18.8h
mls v6.8h, v5.8h, v0.h[0]
trn1 v17.2d, v7.2d, v16.2d
sub v31.8h, v30.8h, v6.8h
trn2 v18.2d, v7.2d, v16.2d
add v30.8h, v30.8h, v6.8h
ldr q7, [x2, #1040]
sqrdmulh v5.8h, v30.8h, v0.h[1]
ldr q16, [x2, #1024]
sqrdmulh v6.8h, v31.8h, v0.h[1]
sqrdmulh v7.8h, v18.8h, v7.8h
sshr v5.8h, v5.8h, #11
mul v16.8h, v18.8h, v16.8h
sshr v6.8h, v6.8h, #11
mls v16.8h, v7.8h, v0.h[0]
mls v30.8h, v5.8h, v0.h[0]
sub v18.8h, v17.8h, v16.8h
mls v31.8h, v6.8h, v0.h[0]
add v17.8h, v17.8h, v16.8h
ldr q19, [x0, #480]
zip1 v5.4s, v30.4s, v31.4s
trn1 v7.4s, v17.4s, v18.4s
ldr q20, [x0, #496]
zip2 v6.4s, v30.4s, v31.4s
trn2 v16.4s, v17.4s, v18.4s
sqrdmulh v21.8h, v20.8h, v4.h[7]
str q5, [x0, #416]
ldr q17, [x2, #1072]
mul v22.8h, v20.8h, v4.h[6]
str q6, [x0, #432]
ldr q18, [x2, #1056]
mls v22.8h, v21.8h, v0.h[0]
sqrdmulh v17.8h, v16.8h, v17.8h
sub v20.8h, v19.8h, v22.8h
mul v18.8h, v16.8h, v18.8h
add v19.8h, v19.8h, v22.8h
mls v18.8h, v17.8h, v0.h[0]
trn1 v21.2d, v19.2d, v20.2d
sub v16.8h, v7.8h, v18.8h
trn2 v22.2d, v19.2d, v20.2d
add v7.8h, v7.8h, v18.8h
ldr q19, [x2, #1104]
sqrdmulh v17.8h, v7.8h, v0.h[1]
ldr q20, [x2, #1088]
sqrdmulh v18.8h, v16.8h, v0.h[1]
sqrdmulh v19.8h, v22.8h, v19.8h
sshr v17.8h, v17.8h, #11
mul v20.8h, v22.8h, v20.8h
sshr v18.8h, v18.8h, #11
mls v20.8h, v19.8h, v0.h[0]
mls v7.8h, v17.8h, v0.h[0]
sub v22.8h, v21.8h, v20.8h
mls v16.8h, v18.8h, v0.h[0]
add v21.8h, v21.8h, v20.8h
zip1 v17.4s, v7.4s, v16.4s
trn1 v19.4s, v21.4s, v22.4s
zip2 v18.4s, v7.4s, v16.4s
trn2 v20.4s, v21.4s, v22.4s
str q17, [x0, #448]
ldr q21, [x2, #1136]
str q18, [x0, #464]
ldr q22, [x2, #1120]
sqrdmulh v21.8h, v20.8h, v21.8h
mul v22.8h, v20.8h, v22.8h
mls v22.8h, v21.8h, v0.h[0]
sub v20.8h, v19.8h, v22.8h
add v19.8h, v19.8h, v22.8h
sqrdmulh v21.8h, v19.8h, v0.h[1]
sqrdmulh v22.8h, v20.8h, v0.h[1]
sshr v21.8h, v21.8h, #11
sshr v22.8h, v22.8h, #11
mls v19.8h, v21.8h, v0.h[0]
mls v20.8h, v22.8h, v0.h[0]
zip1 v21.4s, v19.4s, v20.4s
zip2 v22.4s, v19.4s, v20.4s
str q21, [x0, #480]
str q22, [x0, #496]
ret
.section .rodata
.p2align 4
cr_fwd_c2_t:
.hword 3329
.hword 20159
.hword 63936
.hword 49787
.hword 64787
.hword 58163
.hword 65496
.hword 65142
.hword 64849
.hword 58774
.hword 630
.hword 6201
.hword 64104
.hword 51441
.hword 848
.hword 8347
.hword 1062
.hword 10453
.hword 64126
.hword 51657
.hword 193
.hword 1900
.hword 797
.hword 7845
.hword 64993
.hword 60191
.hword 65467
.hword 64857
.hword 569
.hword 5601
.hword 63953
.hword 49954
.hword 296
.hword 2914
.hword 64654
.hword 56854
.hword 1339
.hword 13180
.hword 1476
.hword 14529
.hword 65253
.hword 62750
.hword 56
.hword 551
.hword 64447
.hword 54817
.hword 1333
.hword 13121
.hword 1426
.hword 14036
.hword 64301
.hword 53380
.hword 535
.hword 5266
.hword 65089
.hword 61136
.hword 64600
.hword 56323
.hword 65086
.hword 61107
.hword 64181
.hword 52198
.hword 821
.hword 8081
.hword 289
.hword 289
.hword 289
.hword 289
.hword 331
.hword 331
.hword 331
.hword 331
.hword 2845
.hword 2845
.hword 2845
.hword 2845
.hword 3258
.hword 3258
.hword 3258
.hword 3258
.hword 17
.hword 17
.hword 64968
.hword 64968
.hword 583
.hword 583
.hword 64856
.hword 64856
.hword 167
.hword 167
.hword 59945
.hword 59945
.hword 5739
.hword 5739
.hword 58843
.hword 58843
.hword 65460
.hword 65460
.hword 65460
.hword 65460
.hword 63963
.hword 63963
.hword 63963
.hword 63963
.hword 64788
.hword 64788
.hword 64788
.hword 64788
.hword 50053
.hword 50053
.hword 50053
.hword 50053
.hword 1637
.hword 1637
.hword 723
.hword 723
.hword 64495
.hword 64495
.hword 1100
.hword 1100
.hword 16113
.hword 16113
.hword 7117
.hword 7117
.hword 55289
.hword 55289
.hword 10828
.hword 10828
.hword 1197
.hword 1197
.hword 1197
.hword 1197
.hword 64511
.hword 64511
.hword 64511
.hword 64511
.hword 11782
.hword 11782
.hword 11782
.hword 11782
.hword 55447
.hword 55447
.hword 55447
.hword 55447
.hword 1409
.hword 1409
.hword 64869
.hword 64869
.hword 65488
.hword 65488
.hword 233
.hword 233
.hword 13869
.hword 13869
.hword 58971
.hword 58971
.hword 65064
.hword 65064
.hword 2293
.hword 2293
.hword 64484
.hword 64484
.hword 64484
.hword 64484
.hword 64262
.hword 64262
.hword 64262
.hword 64262
.hword 55181
.hword 55181
.hword 55181
.hword 55181
.hword 52996
.hword 52996
.hword 52996
.hword 52996
.hword 756
.hword 756
.hword 64363
.hword 64363
.hword 65222
.hword 65222
.hword 65257
.hword 65257
.hword 7441
.hword 7441
.hword 53990
.hword 53990
.hword 62445
.hword 62445
.hword 62790
.hword 62790
.hword 650
.hword 650
.hword 650
.hword 650
.hword 64184
.hword 64184
.hword 64184
.hword 64184
.hword 6398
.hword 6398
.hword 6398
.hword 6398
.hword 52228
.hword 52228
.hword 52228
.hword 52228
.hword 63910
.hword 63910
.hword 1651
.hword 1651
.hword 64996
.hword 64996
.hword 63996
.hword 63996
.hword 49531
.hword 49531
.hword 16251
.hword 16251
.hword 60221
.hword 60221
.hword 50377
.hword 50377
.hword 64720
.hword 64720
.hword 64720
.hword 64720
.hword 632
.hword 632
.hword 632
.hword 632
.hword 57504
.hword 57504
.hword 57504
.hword 57504
.hword 6221
.hword 6221
.hword 6221
.hword 6221
.hword 64054
.hword 64054
.hword 952
.hword 952
.hword 1461
.hword 1461
.hword 64894
.hword 64894
.hword 50948
.hword 50948
.hword 9371
.hword 9371
.hword 14381
.hword 14381
.hword 59217
.hword 59217
.hword 65072
.hword 65072
.hword 65072
.hword 65072
.hword 33
.hword 33
.hword 33
.hword 33
.hword 60969
.hword 60969
.hword 60969
.hword 60969
.hword 325
.hword 325
.hword 325
.hword 325
.hword 939
.hword 939
.hword 64515
.hword 64515
.hword 64644
.hword 64644
.hword 64595
.hword 64595
.hword 9243
.hword 9243
.hword 55486
.hword 55486
.hword 56756
.hword 56756
.hword 56274
.hword 56274
.hword 1320
.hword 1320
.hword 1320
.hword 1320
.hword 64122
.hword 64122
.hword 64122
.hword 64122
.hword 12993
.hword 12993
.hword 12993
.hword 12993
.hword 51618
.hword 51618
.hword 51618
.hword 51618
.hword 733
.hword 733
.hword 64544
.hword 64544
.hword 268
.hword 268
.hword 641
.hword 641
.hword 7215
.hword 7215
.hword 55772
.hword 55772
.hword 2638
.hword 2638
.hword 6309
.hword 6309
.hword 64526
.hword 64526
.hword 64526
.hword 64526
.hword 1435
.hword 1435
.hword 1435
.hword 1435
.hword 55594
.hword 55594
.hword 55594
.hword 55594
.hword 14125
.hword 14125
.hword 14125
.hword 14125
.hword 1584
.hword 1584
.hword 64505
.hword 64505
.hword 64244
.hword 64244
.hword 65427
.hword 65427
.hword 15592
.hword 15592
.hword 55388
.hword 55388
.hword 52819
.hword 52819
.hword 64463
.hword 64463
.hword 807
.hword 807
.hword 807
.hword 807
.hword 452
.hword 452
.hword 452
.hword 452
.hword 7943
.hword 7943
.hword 7943
.hword 7943
.hword 4449
.hword 4449
.hword 4449
.hword 4449
.hword 375
.hword 375
.hword 64756
.hword 64756
.hword 64297
.hword 64297
.hword 1645
.hword 1645
.hword 3691
.hword 3691
.hword 57858
.hword 57858
.hword 53340
.hword 53340
.hword 16192
.hword 16192
.hword 1438
.hword 1438
.hword 1438
.hword 1438
.hword 65075
.hword 65075
.hword 65075
.hword 65075
.hword 14155
.hword 14155
.hword 14155
.hword 14155
.hword 60998
.hword 60998
.hword 60998
.hword 60998
.hword 1063
.hword 1063
.hword 319
.hword 319
.hword 64980
.hword 64980
.hword 757
.hword 757
.hword 10463
.hword 10463
.hword 3140
.hword 3140
.hword 60063
.hword 60063
.hword 7451
.hword 7451
.hword 1534
.hword 1534
.hword 1534
.hword 1534
.hword 64609
.hword 64609
.hword 64609
.hword 64609
.hword 15099
.hword 15099
.hword 15099
.hword 15099
.hword 56411
.hword 56411
.hword 56411
.hword 56411
.hword 64306
.hword 64306
.hword 561
.hword 561
.hword 64673
.hword 64673
.hword 64801
.hword 64801
.hword 53429
.hword 53429
.hword 5522
.hword 5522
.hword 57041
.hword 57041
.hword 58301
.hword 58301
.hword 64854
.hword 64854
.hword 64854
.hword 64854
.hword 64824
.hword 64824
.hword 64824
.hword 64824
.hword 58823
.hword 58823
.hword 58823
.hword 58823
.hword 58528
.hword 58528
.hword 58528
.hword 58528
.hword 65011
.hword 65011
.hword 1092
.hword 1092
.hword 403
.hword 403
.hword 1026
.hword 1026
.hword 60368
.hword 60368
.hword 10749
.hword 10749
.hword 3967
.hword 3967
.hword 10099
.hword 10099
.hword 1481
.hword 1481
.hword 1481
.hword 1481
.hword 648
.hword 648
.hword 648
.hword 648
.hword 14578
.hword 14578
.hword 14578
.hword 14578
.hword 6378
.hword 6378
.hword 6378
.hword 6378
.hword 1143
.hword 1143
.hword 64357
.hword 64357
.hword 64982
.hword 64982
.hword 886
.hword 886
.hword 11251
.hword 11251
.hword 53931
.hword 53931
.hword 60083
.hword 60083
.hword 8721
.hword 8721
.hword 64681
.hword 64681
.hword 64681
.hword 64681
.hword 65317
.hword 65317
.hword 65317
.hword 65317
.hword 57120
.hword 57120
.hword 57120
.hword 57120
.hword 63380
.hword 63380
.hword 63380
.hword 63380
.hword 63929
.hword 63929
.hword 1212
.hword 1212
.hword 64081
.hword 64081
.hword 1029
.hword 1029
.hword 49718
.hword 49718
.hword 11930
.hword 11930
.hword 51214
.hword 51214
.hword 10129
.hword 10129
.hword 1227
.hword 1227
.hword 1227
.hword 1227
.hword 910
.hword 910
.hword 910
.hword 910
.hword 12078
.hword 12078
.hword 12078
.hword 12078
.hword 8957
.hword 8957
.hword 8957
.hword 8957
.hword 64317
.hword 64317
.hword 65142
.hword 65142
.hword 885
.hword 885
.hword 64361
.hword 64361
.hword 53537
.hword 53537
.hword 61658
.hword 61658
.hword 8711
.hword 8711
.hword 53970
.hword 53970
.text
.globl cr_inv_c2
.p2align 4
cr_inv_c2:
adrp x2, cr_inv_c2_t
add x2, x2, :lo12:cr_inv_c2_t
ldr q0, [x2, #64]
ldr q1, [x2, #0]
ldr q2, [x2, #16]
ldr q3, [x2, #32]
ldr q4, [x2, #48]
ldr q16, [x0, #0]
ldr q17, [x0, #16]
uzp1 v18.4s, v16.4s, v17.4s
uzp2 v19.4s, v16.4s, v17.4s
sub v17.8h, v19.8h, v18.8h
add v18.8h, v18.8h, v19.8h
ldr q16, [x2, #112]
ldr q19, [x2, #96]
sqrdmulh v16.8h, v17.8h, v16.8h
mul v19.8h, v17.8h, v19.8h
mls v19.8h, v16.8h, v0.h[0]
trn1 v16.4s, v18.4s, v19.4s
trn2 v17.4s, v18.4s, v19.4s
sub v19.8h, v17.8h, v16.8h
add v16.8h, v16.8h, v17.8h
ldr q18, [x2, #144]
ldr q20, [x0, #32]
ldr q17, [x2, #128]
ldr q21, [x0, #48]
sqrdmulh v18.8h, v19.8h, v18.8h
uzp1 v22.4s, v20.4s, v21.4s
mul v17.8h, v19.8h, v17.8h
uzp2 v23.4s, v20.4s, v21.4s
mls v17.8h, v18.8h, v0.h[0]
sub v21.8h, v23.8h, v22.8h
trn1 v18.2d, v16.2d, v17.2d
add v22.8h, v22.8h, v23.8h
trn2 v19.2d, v16.2d, v17.2d
ldr q20, [x2, #176]
sub v17.8h, v19.8h, v18.8h
ldr q23, [x2, #160]
add v18.8h, v18.8h, v19.8h
sqrdmulh v20.8h, v21.8h, v20.8h
sqrdmulh v16.8h, v17.8h, v1.h[1]
mul v23.8h, v21.8h, v23.8h
mul v19.8h, v17.8h, v1.h[0]
mls v23.8h, v20.8h, v0.h[0]
mls v19.8h, v16.8h, v0.h[0]
trn1 v20.4s, v22.4s, v23.4s
str q18, [x0, #0]
trn2 v21.4s, v22.4s, v23.4s
str q19, [x0, #16]
sub v23.8h, v21.8h, v20.8h
add v20.8h, v20.8h, v21.8h
ldr q22, [x2, #208]
ldr q24, [x0, #64]
ldr q21, [x2, #192]
ldr q25, [x0, #80]
sqrdmulh v22.8h, v23.8h, v22.8h
uzp1 v26.4s, v24.4s, v25.4s
mul v21.8h, v23.8h, v21.8h
uzp2 v27.4s, v24.4s, v25.4s
mls v21.8h, v22.8h, v0.h[0]
sub v25.8h, v27.8h, v26.8h
trn1 v22.2d, v20.2d, v21.2d
add v26.8h, v26.8h, v27.8h
trn2 v23.2d, v20.2d, v21.2d
ldr q24, [x2, #240]
sub v21.8h, v23.8h, v22.8h
ldr q27, [x2, #224]
add v22.8h, v22.8h, v23.8h
sqrdmulh v24.8h, v25.8h, v24.8h
sqrdmulh v20.8h, v21.8h, v1.h[3]
mul v27.8h, v25.8h, v27.8h
mul v23.8h, v21.8h, v1.h[2]
mls v27.8h, v24.8h, v0.h[0]
mls v23.8h, v20.8h, v0.h[0]
trn1 v24.4s, v26.4s, v27.4s
str q22, [x0, #32]
trn2 v25.4s, v26.4s, v27.4s
str q23, [x0, #48]
sub v27.8h, v25.8h, v24.8h
add v24.8h, v24.8h, v25.8h
ldr q26, [x2, #272]
ldr q28, [x0, #96]
ldr q25, [x2, #256]
ldr q29, [x0, #112]
sqrdmulh v26.8h, v27.8h, v26.8h
uzp1 v30.4s, v28.4s, v29.4s
mul v25.8h, v27.8h, v25.8h
uzp2 v31.4s, v28.4s, v29.4s
mls v25.8h, v26.8h, v0.h[0]
sub v29.8h, v31.8h, v30.8h
trn1 v26.2d, v24.2d, v25.2d
add v30.8h, v30.8h, v31.8h
trn2 v27.2d, v24.2d, v25.2d
ldr q28, [x2, #304]
sub v25.8h, v27.8h, v26.8h
ldr q31, [x2, #288]
add v26.8h, v26.8h, v27.8h
sqrdmulh v28.8h, v29.8h, v28.8h
sqrdmulh v24.8h, v25.8h, v1.h[5]
mul v31.8h, v29.8h, v31.8h
mul v27.8h, v25.8h, v1.h[4]
mls v31.8h, v28.8h, v0.h[0]
mls v27.8h, v24.8h, v0.h[0]
trn1 v28.4s, v30.4s, v31.4s
str q26, [x0, #64]
trn2 v29.4s, v30.4s, v31.4s
str q27, [x0, #80]
sub v31.8h, v29.8h, v28.8h
add v28.8h, v28.8h, v29.8h
ldr q30, [x2, #336]
ldr q5, [x0, #128]
ldr q29, [x2, #320]
ldr q6, [x0, #144]
sqrdmulh v30.8h, v31.8h, v30.8h
uzp1 v7.4s, v5.4s, v6.4s
mul v29.8h, v31.8h, v29.8h
uzp2 v16.4s, v5.4s, v6.4s
mls v29.8h, v30.8h, v0.h[0]
sub v6.8h, v16.8h, v7.8h
trn1 v30.2d, v28.2d, v29.2d
add v7.8h, v7.8h, v16.8h
trn2 v31.2d, v28.2d, v29.2d
ldr q5, [x2, #368]
sub v29.8h, v31.8h, v30.8h
ldr q16, [x2, #352]
add v30.8h, v30.8h, v31.8h
sqrdmulh v5.8h, v6.8h, v5.8h
sqrdmulh v28.8h, v29.8h, v1.h[7]
mul v16.8h, v6.8h, v16.8h
mul v31.8h, v29.8h, v1.h[6]
mls v16.8h, v5.8h, v0.h[0]
mls v31.8h, v28.8h, v0.h[0]
trn1 v5.4s, v7.4s, v16.4s
str q30, [x0, #96]
trn2 v6.4s, v7.4s, v16.4s
str q31, [x0, #112]
sub v16.8h, v6.8h, v5.8h
add v5.8h, v5.8h, v6.8h
ldr q7, [x2, #400]
ldr q17, [x0, #160]
ldr q6, [x2, #384]
ldr q18, [x0, #176]
sqrdmulh v7.8h, v16.8h, v7.8h
uzp1 v19.4s, v17.4s, v18.4s
mul v6.8h, v16.8h, v6.8h
uzp2 v20.4s, v17.4s, v18.4s
mls v6.8h, v7.8h, v0.h[0]
sub v18.8h, v20.8h, v19.8h
trn1 v7.2d, v5.2d, v6.2d
add v19.8h, v19.8h, v20.8h
trn2 v16.2d, v5.2d, v6.2d
ldr q17, [x2, #432]
sub v6.8h, v16.8h, v7.8h
ldr q20, [x2, #416]
add v7.8h, v7.8h, v16.8h
sqrdmulh v17.8h, v18.8h, v17.8h
sqrdmulh v5.8h, v6.8h, v2.h[1]
mul v20.8h, v18.8h, v20.8h
mul v16.8h, v6.8h, v2.h[0]
mls v20.8h, v17.8h, v0.h[0]
mls v16.8h, v5.8h, v0.h[0]
trn1 v17.4s, v19.4s, v20.4s
str q7, [x0, #128]
trn2 v18.4s, v19.4s, v20.4s
str q16, [x0, #144]
sub v20.8h, v18.8h, v17.8h
add v17.8h, v17.8h, v18.8h
ldr q19, [x2, #464]
ldr q21, [x0, #192]
ldr q18, [x2, #448]
ldr q22, [x0, #208]
sqrdmulh v19.8h, v20.8h, v19.8h
uzp1 v23.4s, v21.4s, v22.4s
mul v18.8h, v20.8h, v18.8h
uzp2 v24.4s, v21.4s, v22.4s
mls v18.8h, v19.8h, v0.h[0]
sub v22.8h, v24.8h, v23.8h
trn1 v19.2d, v17.2d, v18.2d
add v23.8h, v23.8h, v24.8h
trn2 v20.2d, v17.2d, v18.2d
ldr q21, [x2, #496]
sub v18.8h, v20.8h, v19.8h
ldr q24, [x2, #480]
add v19.8h, v19.8h, v20.8h
sqrdmulh v21.8h, v22.8h, v21.8h
sqrdmulh v17.8h, v18.8h, v2.h[3]
mul v24.8h, v22.8h, v24.8h
mul v20.8h, v18.8h, v2.h[2]
mls v24.8h, v21.8h, v0.h[0]
mls v20.8h, v17.8h, v0.h[0]
trn1 v21.4s, v23.4s, v24.4s
str q19, [x0, #160]
trn2 v22.4s, v23.4s, v24.4s
str q20, [x0, #176]
sub v24.8h, v22.8h, v21.8h
add v21.8h, v21.8h, v22.8h
ldr q23, [x2, #528]
ldr q25, [x0, #224]
ldr q22, [x2, #512]
ldr q26, [x0, #240]
sqrdmulh v23.8h, v24.8h, v23.8h
uzp1 v27.4s, v25.4s, v26.4s
mul v22.8h, v24.8h, v22.8h
uzp2 v28.4s, v25.4s, v26.4s
mls v22.8h, v23.8h, v0.h[0]
sub v26.8h, v28.8h, v27.8h
trn1 v23.2d, v21.2d, v22.2d
add v27.8h, v27.8h, v28.8h
trn2 v24.2d, v21.2d, v22.2d
ldr q25, [x2, #560]
sub v22.8h, v24.8h, v23.8h
ldr q28, [x2, #544]
add v23.8h, v23.8h, v24.8h
sqrdmulh v25.8h, v26.8h, v25.8h
sqrdmulh v21.8h, v22.8h, v2.h[5]
mul v28.8h, v26.8h, v28.8h
mul v24.8h, v22.8h, v2.h[4]
mls v28.8h, v25.8h, v0.h[0]
mls v24.8h, v21.8h, v0.h[0]
trn1 v25.4s, v27.4s, v28.4s
str q23, [x0, #192]
trn2 v26.4s, v27.4s, v28.4s
str q24, [x0, #208]
sub v28.8h, v26.8h, v25.8h
add v25.8h, v25.8h, v26.8h
ldr q27, [x2, #592]
ldr q29, [x0, #256]
ldr q26, [x2, #576]
ldr q30, [x0, #272]
sqrdmulh v27.8h, v28.8h, v27.8h
uzp1 v31.4s, v29.4s, v30.4s
mul v26.8h, v28.8h, v26.8h
uzp2 v5.4s, v29.4s, v30.4s
mls v26.8h, v27.8h, v0.h[0]
sub v30.8h, v5.8h, v31.8h
trn1 v27.2d, v25.2d, v26.2d
add v31.8h, v31.8h, v5.8h
trn2 v28.2d, v25.2d, v26.2d
ldr q29, [x2, #624]
sub v26.8h, v28.8h, v27.8h
ldr q5, [x2, #608]
add v27.8h, v27.8h, v28.8h
sqrdmulh v29.8h, v30.8h, v29.8h
sqrdmulh v25.8h, v26.8h, v2.h[7]
mul v5.8h, v30.8h, v5.8h
mul v28.8h, v26.8h, v2.h[6]
mls v5.8h, v29.8h, v0.h[0]
mls v28.8h, v25.8h, v0.h[0]
trn1 v29.4s, v31.4s, v5.4s
str q27, [x0, #224]
trn2 v30.4s, v31.4s, v5.4s
str q28, [x0, #240]
sub v5.8h, v30.8h, v29.8h
add v29.8h, v29.8h, v30.8h
ldr q31, [x2, #656]
ldr q6, [x0, #288]
ldr q30, [x2, #640]
ldr q7, [x0, #304]
sqrdmulh v31.8h, v5.8h, v31.8h
uzp1 v16.4s, v6.4s, v7.4s
mul v30.8h, v5.8h, v30.8h
uzp2 v17.4s, v6.4s, v7.4s
mls v30.8h, v31.8h, v0.h[0]
sub v7.8h, v17.8h, v16.8h
trn1 v31.2d, v29.2d, v30.2d
add v16.8h, v16.8h, v17.8h
trn2 v5.2d, v29.2d, v30.2d
ldr q6, [x2, #688]
sub v30.8h, v5.8h, v31.8h
ldr q17, [x2, #672]
add v31.8h, v31.8h, v5.8h
sqrdmulh v6.8h, v7.8h, v6.8h
sqrdmulh v29.8h, v30.8h, v3.h[1]
mul v17.8h, v7.8h, v17.8h
mul v5.8h, v30.8h, v3.h[0]
mls v17.8h, v6.8h, v0.h[0]
mls v5.8h, v29.8h, v0.h[0]
trn1 v6.4s, v16.4s, v17.4s
str q31, [x0, #256]
trn2 v7.4s, v16.4s, v17.4s
str q5, [x0, #272]
sub v17.8h, v7.8h, v6.8h
add v6.8h, v6.8h, v7.8h
ldr q16, [x2, #720]
ldr q18, [x0, #320]
ldr q7, [x2, #704]
ldr q19, [x0, #336]
sqrdmulh v16.8h, v17.8h, v16.8h
uzp1 v20.4s, v18.4s, v19.4s
mul v7.8h, v17.8h, v7.8h
uzp2 v21.4s, v18.4s, v19.4s
mls v7.8h, v16.8h, v0.h[0]
sub v19.8h, v21.8h, v20.8h
trn1 v16.2d, v6.2d, v7.2d
add v20.8h, v20.8h, v21.8h
trn2 v17.2d, v6.2d, v7.2d
ldr q18, [x2, #752]
sub v7.8h, v17.8h, v16.8h
ldr q21, [x2, #736]
add v16.8h, v16.8h, v17.8h
sqrdmulh v18.8h, v19.8h, v18.8h
sqrdmulh v6.8h, v7.8h, v3.h[3]
mul v21.8h, v19.8h, v21.8h
mul v17.8h, v7.8h, v3.h[2]
mls v21.8h, v18.8h, v0.h[0]
mls v17.8h, v6.8h, v0.h[0]
trn1 v18.4s, v20.4s, v21.4s
str q16, [x0, #288]
trn2 v19.4s, v20.4s, v21.4s
str q17, [x0, #304]
sub v21.8h, v19.8h, v18.8h
add v18.8h, v18.8h, v19.8h
ldr q20, [x2, #784]
ldr q22, [x0, #352]
ldr q19, [x2, #768]
ldr q23, [x0, #368]
sqrdmulh v20.8h, v21.8h, v20.8h
uzp1 v24.4s, v22.4s, v23.4s
mul v19.8h, v21.8h, v19.8h
uzp2 v25.4s, v22.4s, v23.4s
mls v19.8h, v20.8h, v0.h[0]
sub v23.8h, v25.8h, v24.8h
trn1 v20.2d, v18.2d, v19.2d
add v24.8h, v24.8h, v25.8h
trn2 v21.2d, v18.2d, v19.2d
ldr q22, [x2, #816]
sub v19.8h, v21.8h, v20.8h
ldr q25, [x2, #800]
add v20.8h, v20.8h, v21.8h
sqrdmulh v22.8h, v23.8h, v22.8h
sqrdmulh v18.8h, v19.8h, v3.h[5]
mul v25.8h, v23.8h, v25.8h
mul v21.8h, v19.8h, v3.h[4]
mls v25.8h, v22.8h, v0.h[0]
mls v21.8h, v18.8h, v0.h[0]
trn1 v22.4s, v24.4s, v25.4s
str q20, [x0, #320]
trn2 v23.4s, v24.4s, v25.4s
str q21, [x0, #336]
sub v25.8h, v23.8h, v22.8h
add v22.8h, v22.8h, v23.8h
ldr q24, [x2, #848]
ldr q26, [x0, #384]
ldr q23, [x2, #832]
ldr q27, [x0, #400]
sqrdmulh v24.8h, v25.8h, v24.8h
uzp1 v28.4s, v26.4s, v27.4s
mul v23.8h, v25.8h, v23.8h
uzp2 v29.4s, v26.4s, v27.4s
mls v23.8h, v24.8h, v0.h[0]
sub v27.8h, v29.8h, v28.8h
trn1 v24.2d, v22.2d, v23.2d
add v28.8h, v28.8h, v29.8h
trn2 v25.2d, v22.2d, v23.2d
ldr q26, [x2, #880]
sub v23.8h, v25.8h, v24.8h
ldr q29, [x2, #864]
add v24.8h, v24.8h, v25.8h
sqrdmulh v26.8h, v27.8h, v26.8h
sqrdmulh v22.8h, v23.8h, v3.h[7]
mul v29.8h, v27.8h, v29.8h
mul v25.8h, v23.8h, v3.h[6]
mls v29.8h, v26.8h, v0.h[0]
mls v25.8h, v22.8h, v0.h[0]
trn1 v26.4s, v28.4s, v29.4s
str q24, [x0, #352]
trn2 v27.4s, v28.4s, v29.4s
str q25, [x0, #368]
sub v29.8h, v27.8h, v26.8h
add v26.8h, v26.8h, v27.8h
ldr q28, [x2, #912]
ldr q30, [x0, #416]
ldr q27, [x2, #896]
ldr q31, [x0, #432]
sqrdmulh v28.8h, v29.8h, v28.8h
uzp1 v5.4s, v30.4s, v31.4s
mul v27.8h, v29.8h, v27.8h
uzp2 v6.4s, v30.4s, v31.4s
mls v27.8h, v28.8h, v0.h[0]
sub v31.8h, v6.8h, v5.8h
trn1 v28.2d, v26.2d, v27.2d
add v5.8h, v5.8h, v6.8h
trn2 v29.2d, v26.2d, v27.2d
ldr q30, [x2, #944]
sub v27.8h, v29.8h, v28.8h
ldr q6, [x2, #928]
add v28.8h, v28.8h, v29.8h
sqrdmulh v30.8h, v31.8h, v30.8h
sqrdmulh v26.8h, v27.8h, v4.h[1]
mul v6.8h, v31.8h, v6.8h
mul v29.8h, v27.8h, v4.h[0]
mls v6.8h, v30.8h, v0.h[0]
mls v29.8h, v26.8h, v0.h[0]
trn1 v30.4s, v5.4s, v6.4s
str q28, [x0, #384]
trn2 v31.4s, v5.4s, v6.4s
str q29, [x0, #400]
sub v6.8h, v31.8h, v30.8h
add v30.8h, v30.8h, v31.8h
ldr q5, [x2, #976]
ldr q7, [x0, #448]
ldr q31, [x2, #960]
ldr q16, [x0, #464]
sqrdmulh v5.8h, v6.8h, v5.8h
uzp1 v17.4s, v7.4s, v16.4s
mul v31.8h, v6.8h, v31.8h
uzp2 v18.4s, v7.4s, v16.4s
mls v31.8h, v5.8h, v0.h[0]
sub v16.8h, v18.8h, v17.8h
trn1 v5.2d, v30.2d, v31.2d
add v17.8h, v17.8h, v18.8h
trn2 v6.2d, v30.2d, v31.2d
ldr q7, [x2, #1008]
sub v31.8h, v6.8h, v5.8h
ldr q18, [x2, #992]
add v5.8h, v5.8h, v6.8h
sqrdmulh v7.8h, v16.8h, v7.8h
sqrdmulh v30.8h, v31.8h, v4.h[3]
mul v18.8h, v16.8h, v18.8h
mul v6.8h, v31.8h, v4.h[2]
mls v18.8h, v7.8h, v0.h[0]
mls v6.8h, v30.8h, v0.h[0]
trn1 v7.4s, v17.4s, v18.4s
str q5, [x0, #416]
trn2 v16.4s, v17.4s, v18.4s
str q6, [x0, #432]
sub v18.8h, v16.8h, v7.8h
add v7.8h, v7.8h, v16.8h
ldr q17, [x2, #1040]
ldr q19, [x0, #480]
ldr q16, [x2, #1024]
ldr q20, [x0, #496]
sqrdmulh v17.8h, v18.8h, v17.8h
uzp1 v21.4s, v19.4s, v20.4s
mul v16.8h, v18.8h, v16.8h
uzp2 v22.4s, v19.4s, v20.4s
mls v16.8h, v17.8h, v0.h[0]
sub v20.8h, v22.8h, v21.8h
trn1 v17.2d, v7.2d, v16.2d
add v21.8h, v21.8h, v22.8h
trn2 v18.2d, v7.2d, v16.2d
ldr q19, [x2, #1072]
sub v16.8h, v18.8h, v17.8h
ldr q22, [x2, #1056]
add v17.8h, v17.8h, v18.8h
sqrdmulh v19.8h, v20.8h, v19.8h
sqrdmulh v7.8h, v16.8h, v4.h[5]
mul v22.8h, v20.8h, v22.8h
mul v18.8h, v16.8h, v4.h[4]
mls v22.8h, v19.8h, v0.h[0]
mls v18.8h, v7.8h, v0.h[0]
trn1 v19.4s, v21.4s, v22.4s
str q17, [x0, #448]
trn2 v20.4s, v21.4s, v22.4s
str q18, [x0, #464]
sub v22.8h, v20.8h, v19.8h
add v19.8h, v19.8h, v20.8h
ldr q21, [x2, #1104]
ldr q20, [x2, #1088]
sqrdmulh v21.8h, v22.8h, v21.8h
mul v20.8h, v22.8h, v20.8h
mls v20.8h, v21.8h, v0.h[0]
trn1 v21.2d, v19.2d, v20.2d
trn2 v22.2d, v19.2d, v20.2d
sub v20.8h, v22.8h, v21.8h
add v21.8h, v21.8h, v22.8h
sqrdmulh v19.8h, v20.8h, v4.h[7]
mul v22.8h, v20.8h, v4.h[6]
mls v22.8h, v19.8h, v0.h[0]
str q21, [x0, #480]
str q22, [x0, #496]
ldr q1, [x2, #80]
ldr q16, [x0, #0]
ldr q17, [x0, #32]
ldr q18, [x0, #64]
ldr q19, [x0, #96]
ldr q20, [x0, #128]
ldr q21, [x0, #160]
ldr q22, [x0, #192]
ldr q23, [x0, #224]
ldr q24, [x0, #256]
ldr q25, [x0, #288]
ldr q26, [x0, #320]
ldr q27, [x0, #352]
ldr q28, [x0, #384]
ldr q29, [x0, #416]
ldr q30, [x0, #448]
ldr q31, [x0, #480]
ldr q2, [x2, #1120]
ldr q3, [x2, #1136]
ldr q4, [x2, #1152]
ldr q7, [x2, #1168]
sub v5.8h, v17.8h, v16.8h
add v16.8h, v16.8h, v17.8h
sub v16.8h, v16.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v3.h[7]
mul v17.8h, v5.8h, v3.h[6]
mls v17.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v16.8h, v4.h[1]
mul v16.8h, v16.8h, v4.h[0]
mls v16.8h, v6.8h, v0.h[0]
sub v5.8h, v19.8h, v18.8h
add v18.8h, v18.8h, v19.8h
sub v18.8h, v18.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v3.h[5]
mul v19.8h, v5.8h, v3.h[4]
mls v19.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v18.8h, v4.h[1]
mul v18.8h, v18.8h, v4.h[0]
mls v18.8h, v6.8h, v0.h[0]
sub v5.8h, v21.8h, v20.8h
add v20.8h, v20.8h, v21.8h
sub v20.8h, v20.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v3.h[3]
mul v21.8h, v5.8h, v3.h[2]
mls v21.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v20.8h, v4.h[1]
mul v20.8h, v20.8h, v4.h[0]
mls v20.8h, v6.8h, v0.h[0]
sub v5.8h, v23.8h, v22.8h
add v22.8h, v22.8h, v23.8h
sub v22.8h, v22.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v3.h[1]
mul v23.8h, v5.8h, v3.h[0]
mls v23.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v22.8h, v4.h[1]
mul v22.8h, v22.8h, v4.h[0]
mls v22.8h, v6.8h, v0.h[0]
sub v5.8h, v25.8h, v24.8h
add v24.8h, v24.8h, v25.8h
sub v24.8h, v24.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v2.h[7]
mul v25.8h, v5.8h, v2.h[6]
mls v25.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v24.8h, v4.h[1]
mul v24.8h, v24.8h, v4.h[0]
mls v24.8h, v6.8h, v0.h[0]
sub v5.8h, v27.8h, v26.8h
add v26.8h, v26.8h, v27.8h
sub v26.8h, v26.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v27.8h, v5.8h, v2.h[4]
mls v27.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v26.8h, v4.h[1]
mul v26.8h, v26.8h, v4.h[0]
mls v26.8h, v6.8h, v0.h[0]
sub v5.8h, v29.8h, v28.8h
add v28.8h, v28.8h, v29.8h
sub v28.8h, v28.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v2.h[3]
mul v29.8h, v5.8h, v2.h[2]
mls v29.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v28.8h, v4.h[1]
mul v28.8h, v28.8h, v4.h[0]
mls v28.8h, v6.8h, v0.h[0]
sub v5.8h, v31.8h, v30.8h
add v30.8h, v30.8h, v31.8h
sub v30.8h, v30.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v2.h[1]
mul v31.8h, v5.8h, v2.h[0]
mls v31.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v30.8h, v4.h[1]
mul v30.8h, v30.8h, v4.h[0]
mls v30.8h, v6.8h, v0.h[0]
sub v2.8h, v18.8h, v16.8h
sub v4.8h, v19.8h, v17.8h
add v16.8h, v16.8h, v18.8h
add v17.8h, v17.8h, v19.8h
sqrdmulh v3.8h, v2.8h, v1.h[7]
sqrdmulh v5.8h, v4.8h, v1.h[7]
mul v18.8h, v2.8h, v1.h[6]
mul v19.8h, v4.8h, v1.h[6]
mls v18.8h, v3.8h, v0.h[0]
mls v19.8h, v5.8h, v0.h[0]
sub v2.8h, v22.8h, v20.8h
sub v4.8h, v23.8h, v21.8h
add v20.8h, v20.8h, v22.8h
add v21.8h, v21.8h, v23.8h
sqrdmulh v3.8h, v2.8h, v1.h[5]
sqrdmulh v5.8h, v4.8h, v1.h[5]
mul v22.8h, v2.8h, v1.h[4]
mul v23.8h, v4.8h, v1.h[4]
mls v22.8h, v3.8h, v0.h[0]
mls v23.8h, v5.8h, v0.h[0]
sub v2.8h, v26.8h, v24.8h
sub v4.8h, v27.8h, v25.8h
add v24.8h, v24.8h, v26.8h
add v25.8h, v25.8h, v27.8h
sqrdmulh v3.8h, v2.8h, v1.h[3]
sqrdmulh v5.8h, v4.8h, v1.h[3]
mul v26.8h, v2.8h, v1.h[2]
mul v27.8h, v4.8h, v1.h[2]
mls v26.8h, v3.8h, v0.h[0]
mls v27.8h, v5.8h, v0.h[0]
sub v2.8h, v30.8h, v28.8h
sub v4.8h, v31.8h, v29.8h
add v28.8h, v28.8h, v30.8h
add v29.8h, v29.8h, v31.8h
sqrdmulh v3.8h, v2.8h, v1.h[1]
sqrdmulh v5.8h, v4.8h, v1.h[1]
mul v30.8h, v2.8h, v1.h[0]
mul v31.8h, v4.8h, v1.h[0]
mls v30.8h, v3.8h, v0.h[0]
mls v31.8h, v5.8h, v0.h[0]
sub v2.8h, v20.8h, v16.8h
sub v4.8h, v21.8h, v17.8h
add v16.8h, v16.8h, v20.8h
add v17.8h, v17.8h, v21.8h
sqrdmulh v3.8h, v2.8h, v0.h[7]
sqrdmulh v5.8h, v4.8h, v0.h[7]
mul v20.8h, v2.8h, v0.h[6]
mul v21.8h, v4.8h, v0.h[6]
mls v20.8h, v3.8h, v0.h[0]
mls v21.8h, v5.8h, v0.h[0]
sub v2.8h, v22.8h, v18.8h
sub v4.8h, v23.8h, v19.8h
add v18.8h, v18.8h, v22.8h
add v19.8h, v19.8h, v23.8h
sqrdmulh v3.8h, v2.8h, v0.h[7]
sqrdmulh v5.8h, v4.8h, v0.h[7]
mul v22.8h, v2.8h, v0.h[6]
mul v23.8h, v4.8h, v0.h[6]
mls v22.8h, v3.8h, v0.h[0]
mls v23.8h, v5.8h, v0.h[0]
sub v2.8h, v28.8h, v24.8h
sub v4.8h, v29.8h, v25.8h
add v24.8h, v24.8h, v28.8h
add v25.8h, v25.8h, v29.8h
sqrdmulh v3.8h, v2.8h, v0.h[5]
sqrdmulh v5.8h, v4.8h, v0.h[5]
mul v28.8h, v2.8h, v0.h[4]
mul v29.8h, v4.8h, v0.h[4]
mls v28.8h, v3.8h, v0.h[0]
mls v29.8h, v5.8h, v0.h[0]
sub v2.8h, v30.8h, v26.8h
sub v4.8h, v31.8h, v27.8h
add v26.8h, v26.8h, v30.8h
add v27.8h, v27.8h, v31.8h
sqrdmulh v3.8h, v2.8h, v0.h[5]
sqrdmulh v5.8h, v4.8h, v0.h[5]
mul v30.8h, v2.8h, v0.h[4]
mul v31.8h, v4.8h, v0.h[4]
mls v30.8h, v3.8h, v0.h[0]
mls v31.8h, v5.8h, v0.h[0]
ldr q7, [x2, #1184]
sub v2.8h, v24.8h, v16.8h
sub v4.8h, v25.8h, v17.8h
add v16.8h, v16.8h, v24.8h
add v17.8h, v17.8h, v25.8h
sqrdmulh v3.8h, v2.8h, v0.h[3]
sqrdmulh v5.8h, v4.8h, v0.h[3]
mul v24.8h, v2.8h, v0.h[2]
mul v25.8h, v4.8h, v0.h[2]
mls v24.8h, v3.8h, v0.h[0]
mls v25.8h, v5.8h, v0.h[0]
sqrdmulh v2.8h, v16.8h, v0.h[1]
sqrdmulh v4.8h, v17.8h, v0.h[1]
sshr v2.8h, v2.8h, #11
sshr v4.8h, v4.8h, #11
sshr v3.8h, v24.8h, #15
sshr v5.8h, v25.8h, #15
mls v16.8h, v2.8h, v0.h[0]
mls v17.8h, v4.8h, v0.h[0]
and v3.16b, v3.16b, v7.16b
and v5.16b, v5.16b, v7.16b
add v24.8h, v24.8h, v3.8h
add v25.8h, v25.8h, v5.8h
sub v2.8h, v26.8h, v18.8h
sub v4.8h, v27.8h, v19.8h
add v18.8h, v18.8h, v26.8h
add v19.8h, v19.8h, v27.8h
sqrdmulh v3.8h, v2.8h, v0.h[3]
sqrdmulh v5.8h, v4.8h, v0.h[3]
mul v26.8h, v2.8h, v0.h[2]
mul v27.8h, v4.8h, v0.h[2]
mls v26.8h, v3.8h, v0.h[0]
mls v27.8h, v5.8h, v0.h[0]
sqrdmulh v2.8h, v18.8h, v0.h[1]
sqrdmulh v4.8h, v19.8h, v0.h[1]
sshr v2.8h, v2.8h, #11
sshr v4.8h, v4.8h, #11
sshr v3.8h, v26.8h, #15
sshr v5.8h, v27.8h, #15
mls v18.8h, v2.8h, v0.h[0]
mls v19.8h, v4.8h, v0.h[0]
and v3.16b, v3.16b, v7.16b
and v5.16b, v5.16b, v7.16b
add v26.8h, v26.8h, v3.8h
add v27.8h, v27.8h, v5.8h
sub v2.8h, v28.8h, v20.8h
sub v4.8h, v29.8h, v21.8h
add v20.8h, v20.8h, v28.8h
add v21.8h, v21.8h, v29.8h
sqrdmulh v3.8h, v2.8h, v0.h[3]
sqrdmulh v5.8h, v4.8h, v0.h[3]
mul v28.8h, v2.8h, v0.h[2]
mul v29.8h, v4.8h, v0.h[2]
mls v28.8h, v3.8h, v0.h[0]
mls v29.8h, v5.8h, v0.h[0]
sqrdmulh v2.8h, v20.8h, v0.h[1]
sqrdmulh v4.8h, v21.8h, v0.h[1]
sshr v2.8h, v2.8h, #11
sshr v4.8h, v4.8h, #11
sshr v3.8h, v28.8h, #15
sshr v5.8h, v29.8h, #15
mls v20.8h, v2.8h, v0.h[0]
mls v21.8h, v4.8h, v0.h[0]
and v3.16b, v3.16b, v7.16b
and v5.16b, v5.16b, v7.16b
add v28.8h, v28.8h, v3.8h
add v29.8h, v29.8h, v5.8h
sub v2.8h, v30.8h, v22.8h
sub v4.8h, v31.8h, v23.8h
add v22.8h, v22.8h, v30.8h
add v23.8h, v23.8h, v31.8h
sqrdmulh v3.8h, v2.8h, v0.h[3]
sqrdmulh v5.8h, v4.8h, v0.h[3]
mul v30.8h, v2.8h, v0.h[2]
mul v31.8h, v4.8h, v0.h[2]
mls v30.8h, v3.8h, v0.h[0]
mls v31.8h, v5.8h, v0.h[0]
sqrdmulh v2.8h, v22.8h, v0.h[1]
sqrdmulh v4.8h, v23.8h, v0.h[1]
sshr v2.8h, v2.8h, #11
sshr v4.8h, v4.8h, #11
sshr v3.8h, v30.8h, #15
sshr v5.8h, v31.8h, #15
mls v22.8h, v2.8h, v0.h[0]
mls v23.8h, v4.8h, v0.h[0]
and v3.16b, v3.16b, v7.16b
and v5.16b, v5.16b, v7.16b
add v30.8h, v30.8h, v3.8h
add v31.8h, v31.8h, v5.8h
str q16, [x0, #0]
str q17, [x0, #32]
str q18, [x0, #64]
str q19, [x0, #96]
str q20, [x0, #128]
str q21, [x0, #160]
str q22, [x0, #192]
str q23, [x0, #224]
str q24, [x0, #256]
str q25, [x0, #288]
str q26, [x0, #320]
str q27, [x0, #352]
str q28, [x0, #384]
str q29, [x0, #416]
str q30, [x0, #448]
str q31, [x0, #480]
ldr q16, [x0, #16]
ldr q17, [x0, #48]
ldr q18, [x0, #80]
ldr q19, [x0, #112]
ldr q20, [x0, #144]
ldr q21, [x0, #176]
ldr q22, [x0, #208]
ldr q23, [x0, #240]
ldr q24, [x0, #272]
ldr q25, [x0, #304]
ldr q26, [x0, #336]
ldr q27, [x0, #368]
ldr q28, [x0, #400]
ldr q29, [x0, #432]
ldr q30, [x0, #464]
ldr q31, [x0, #496]
ldr q2, [x2, #1120]
ldr q3, [x2, #1136]
ldr q4, [x2, #1152]
sub v5.8h, v17.8h, v16.8h
add v16.8h, v16.8h, v17.8h
sqrdmulh v6.8h, v5.8h, v3.h[7]
mul v17.8h, v5.8h, v3.h[6]
mls v17.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v16.8h, v4.h[1]
mul v16.8h, v16.8h, v4.h[0]
mls v16.8h, v6.8h, v0.h[0]
sub v5.8h, v19.8h, v18.8h
add v18.8h, v18.8h, v19.8h
sqrdmulh v6.8h, v5.8h, v3.h[5]
mul v19.8h, v5.8h, v3.h[4]
mls v19.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v18.8h, v4.h[1]
mul v18.8h, v18.8h, v4.h[0]
mls v18.8h, v6.8h, v0.h[0]
sub v5.8h, v21.8h, v20.8h
add v20.8h, v20.8h, v21.8h
sqrdmulh v6.8h, v5.8h, v3.h[3]
mul v21.8h, v5.8h, v3.h[2]
mls v21.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v20.8h, v4.h[1]
mul v20.8h, v20.8h, v4.h[0]
mls v20.8h, v6.8h, v0.h[0]
sub v5.8h, v23.8h, v22.8h
add v22.8h, v22.8h, v23.8h
sqrdmulh v6.8h, v5.8h, v3.h[1]
mul v23.8h, v5.8h, v3.h[0]
mls v23.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v22.8h, v4.h[1]
mul v22.8h, v22.8h, v4.h[0]
mls v22.8h, v6.8h, v0.h[0]
sub v5.8h, v25.8h, v24.8h
add v24.8h, v24.8h, v25.8h
sqrdmulh v6.8h, v5.8h, v2.h[7]
mul v25.8h, v5.8h, v2.h[6]
mls v25.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v24.8h, v4.h[1]
mul v24.8h, v24.8h, v4.h[0]
mls v24.8h, v6.8h, v0.h[0]
sub v5.8h, v27.8h, v26.8h
add v26.8h, v26.8h, v27.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v27.8h, v5.8h, v2.h[4]
mls v27.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v26.8h, v4.h[1]
mul v26.8h, v26.8h, v4.h[0]
mls v26.8h, v6.8h, v0.h[0]
sub v5.8h, v29.8h, v28.8h
add v28.8h, v28.8h, v29.8h
sqrdmulh v6.8h, v5.8h, v2.h[3]
mul v29.8h, v5.8h, v2.h[2]
mls v29.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v28.8h, v4.h[1]
mul v28.8h, v28.8h, v4.h[0]
mls v28.8h, v6.8h, v0.h[0]
sub v5.8h, v31.8h, v30.8h
add v30.8h, v30.8h, v31.8h
sqrdmulh v6.8h, v5.8h, v2.h[1]
mul v31.8h, v5.8h, v2.h[0]
mls v31.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v30.8h, v4.h[1]
mul v30.8h, v30.8h, v4.h[0]
mls v30.8h, v6.8h, v0.h[0]
sub v2.8h, v18.8h, v16.8h
sub v4.8h, v19.8h, v17.8h
add v16.8h, v16.8h, v18.8h
add v17.8h, v17.8h, v19.8h
sqrdmulh v3.8h, v2.8h, v1.h[7]
sqrdmulh v5.8h, v4.8h, v1.h[7]
mul v18.8h, v2.8h, v1.h[6]
mul v19.8h, v4.8h, v1.h[6]
mls v18.8h, v3.8h, v0.h[0]
mls v19.8h, v5.8h, v0.h[0]
sub v2.8h, v22.8h, v20.8h
sub v4.8h, v23.8h, v21.8h
add v20.8h, v20.8h, v22.8h
add v21.8h, v21.8h, v23.8h
sqrdmulh v3.8h, v2.8h, v1.h[5]
sqrdmulh v5.8h, v4.8h, v1.h[5]
mul v22.8h, v2.8h, v1.h[4]
mul v23.8h, v4.8h, v1.h[4]
mls v22.8h, v3.8h, v0.h[0]
mls v23.8h, v5.8h, v0.h[0]
sub v2.8h, v26.8h, v24.8h
sub v4.8h, v27.8h, v25.8h
add v24.8h, v24.8h, v26.8h
add v25.8h, v25.8h, v27.8h
sqrdmulh v3.8h, v2.8h, v1.h[3]
sqrdmulh v5.8h, v4.8h, v1.h[3]
mul v26.8h, v2.8h, v1.h[2]
mul v27.8h, v4.8h, v1.h[2]
mls v26.8h, v3.8h, v0.h[0]
mls v27.8h, v5.8h, v0.h[0]
sub v2.8h, v30.8h, v28.8h
sub v4.8h, v31.8h, v29.8h
add v28.8h, v28.8h, v30.8h
add v29.8h, v29.8h, v31.8h
sqrdmulh v3.8h, v2.8h, v1.h[1]
sqrdmulh v5.8h, v4.8h, v1.h[1]
mul v30.8h, v2.8h, v1.h[0]
mul v31.8h, v4.8h, v1.h[0]
mls v30.8h, v3.8h, v0.h[0]
mls v31.8h, v5.8h, v0.h[0]
sub v2.8h, v20.8h, v16.8h
sub v4.8h, v21.8h, v17.8h
add v16.8h, v16.8h, v20.8h
add v17.8h, v17.8h, v21.8h
sqrdmulh v3.8h, v2.8h, v0.h[7]
sqrdmulh v5.8h, v4.8h, v0.h[7]
mul v20.8h, v2.8h, v0.h[6]
mul v21.8h, v4.8h, v0.h[6]
mls v20.8h, v3.8h, v0.h[0]
mls v21.8h, v5.8h, v0.h[0]
sub v2.8h, v22.8h, v18.8h
sub v4.8h, v23.8h, v19.8h
add v18.8h, v18.8h, v22.8h
add v19.8h, v19.8h, v23.8h
sqrdmulh v3.8h, v2.8h, v0.h[7]
sqrdmulh v5.8h, v4.8h, v0.h[7]
mul v22.8h, v2.8h, v0.h[6]
mul v23.8h, v4.8h, v0.h[6]
mls v22.8h, v3.8h, v0.h[0]
mls v23.8h, v5.8h, v0.h[0]
sub v2.8h, v28.8h, v24.8h
sub v4.8h, v29.8h, v25.8h
add v24.8h, v24.8h, v28.8h
add v25.8h, v25.8h, v29.8h
sqrdmulh v3.8h, v2.8h, v0.h[5]
sqrdmulh v5.8h, v4.8h, v0.h[5]
mul v28.8h, v2.8h, v0.h[4]
mul v29.8h, v4.8h, v0.h[4]
mls v28.8h, v3.8h, v0.h[0]
mls v29.8h, v5.8h, v0.h[0]
sub v2.8h, v30.8h, v26.8h
sub v4.8h, v31.8h, v27.8h
add v26.8h, v26.8h, v30.8h
add v27.8h, v27.8h, v31.8h
sqrdmulh v3.8h, v2.8h, v0.h[5]
sqrdmulh v5.8h, v4.8h, v0.h[5]
mul v30.8h, v2.8h, v0.h[4]
mul v31.8h, v4.8h, v0.h[4]
mls v30.8h, v3.8h, v0.h[0]
mls v31.8h, v5.8h, v0.h[0]
ldr q7, [x2, #1184]
sub v2.8h, v24.8h, v16.8h
sub v4.8h, v25.8h, v17.8h
add v16.8h, v16.8h, v24.8h
add v17.8h, v17.8h, v25.8h
sqrdmulh v3.8h, v2.8h, v0.h[3]
sqrdmulh v5.8h, v4.8h, v0.h[3]
mul v24.8h, v2.8h, v0.h[2]
mul v25.8h, v4.8h, v0.h[2]
mls v24.8h, v3.8h, v0.h[0]
mls v25.8h, v5.8h, v0.h[0]
sqrdmulh v2.8h, v16.8h, v0.h[1]
sqrdmulh v4.8h, v17.8h, v0.h[1]
sshr v2.8h, v2.8h, #11
sshr v4.8h, v4.8h, #11
sshr v3.8h, v24.8h, #15
sshr v5.8h, v25.8h, #15
mls v16.8h, v2.8h, v0.h[0]
mls v17.8h, v4.8h, v0.h[0]
and v3.16b, v3.16b, v7.16b
and v5.16b, v5.16b, v7.16b
add v24.8h, v24.8h, v3.8h
add v25.8h, v25.8h, v5.8h
sub v2.8h, v26.8h, v18.8h
sub v4.8h, v27.8h, v19.8h
add v18.8h, v18.8h, v26.8h
add v19.8h, v19.8h, v27.8h
sqrdmulh v3.8h, v2.8h, v0.h[3]
sqrdmulh v5.8h, v4.8h, v0.h[3]
mul v26.8h, v2.8h, v0.h[2]
mul v27.8h, v4.8h, v0.h[2]
mls v26.8h, v3.8h, v0.h[0]
mls v27.8h, v5.8h, v0.h[0]
sqrdmulh v2.8h, v18.8h, v0.h[1]
sqrdmulh v4.8h, v19.8h, v0.h[1]
sshr v2.8h, v2.8h, #11
sshr v4.8h, v4.8h, #11
sshr v3.8h, v26.8h, #15
sshr v5.8h, v27.8h, #15
mls v18.8h, v2.8h, v0.h[0]
mls v19.8h, v4.8h, v0.h[0]
and v3.16b, v3.16b, v7.16b
and v5.16b, v5.16b, v7.16b
add v26.8h, v26.8h, v3.8h
add v27.8h, v27.8h, v5.8h
sub v2.8h, v28.8h, v20.8h
sub v4.8h, v29.8h, v21.8h
add v20.8h, v20.8h, v28.8h
add v21.8h, v21.8h, v29.8h
sqrdmulh v3.8h, v2.8h, v0.h[3]
sqrdmulh v5.8h, v4.8h, v0.h[3]
mul v28.8h, v2.8h, v0.h[2]
mul v29.8h, v4.8h, v0.h[2]
mls v28.8h, v3.8h, v0.h[0]
mls v29.8h, v5.8h, v0.h[0]
sqrdmulh v2.8h, v20.8h, v0.h[1]
sqrdmulh v4.8h, v21.8h, v0.h[1]
sshr v2.8h, v2.8h, #11
sshr v4.8h, v4.8h, #11
sshr v3.8h, v28.8h, #15
sshr v5.8h, v29.8h, #15
mls v20.8h, v2.8h, v0.h[0]
mls v21.8h, v4.8h, v0.h[0]
and v3.16b, v3.16b, v7.16b
and v5.16b, v5.16b, v7.16b
add v28.8h, v28.8h, v3.8h
add v29.8h, v29.8h, v5.8h
sub v2.8h, v30.8h, v22.8h
sub v4.8h, v31.8h, v23.8h
add v22.8h, v22.8h, v30.8h
add v23.8h, v23.8h, v31.8h
sqrdmulh v3.8h, v2.8h, v0.h[3]
sqrdmulh v5.8h, v4.8h, v0.h[3]
mul v30.8h, v2.8h, v0.h[2]
mul v31.8h, v4.8h, v0.h[2]
mls v30.8h, v3.8h, v0.h[0]
mls v31.8h, v5.8h, v0.h[0]
sqrdmulh v2.8h, v22.8h, v0.h[1]
sqrdmulh v4.8h, v23.8h, v0.h[1]
sshr v2.8h, v2.8h, #11
sshr v4.8h, v4.8h, #11
sshr v3.8h, v30.8h, #15
sshr v5.8h, v31.8h, #15
mls v22.8h, v2.8h, v0.h[0]
mls v23.8h, v4.8h, v0.h[0]
and v3.16b, v3.16b, v7.16b
and v5.16b, v5.16b, v7.16b
add v30.8h, v30.8h, v3.8h
add v31.8h, v31.8h, v5.8h
str q16, [x0, #16]
str q17, [x0, #48]
str q18, [x0, #80]
str q19, [x0, #112]
str q20, [x0, #144]
str q21, [x0, #176]
str q22, [x0, #208]
str q23, [x0, #240]
str q24, [x0, #272]
str q25, [x0, #304]
str q26, [x0, #336]
str q27, [x0, #368]
str q28, [x0, #400]
str q29, [x0, #432]
str q30, [x0, #464]
str q31, [x0, #496]
ret
.section .rodata
.p2align 4
cr_inv_c2_t:
.hword 821
.hword 8081
.hword 64181
.hword 52198
.hword 65086
.hword 61107
.hword 64600
.hword 56323
.hword 65089
.hword 61136
.hword 535
.hword 5266
.hword 64301
.hword 53380
.hword 1426
.hword 14036
.hword 1333
.hword 13121
.hword 64447
.hword 54817
.hword 56
.hword 551
.hword 65253
.hword 62750
.hword 1476
.hword 14529
.hword 1339
.hword 13180
.hword 64654
.hword 56854
.hword 296
.hword 2914
.hword 3329
.hword 20159
.hword 63936
.hword 49787
.hword 64787
.hword 58163
.hword 65496
.hword 65142
.hword 64849
.hword 58774
.hword 630
.hword 6201
.hword 64104
.hword 51441
.hword 848
.hword 8347
.hword 64361
.hword 64361
.hword 885
.hword 885
.hword 65142
.hword 65142
.hword 64317
.hword 64317
.hword 53970
.hword 53970
.hword 8711
.hword 8711
.hword 61658
.hword 61658
.hword 53537
.hword 53537
.hword 910
.hword 910
.hword 910
.hword 910
.hword 1227
.hword 1227
.hword 1227
.hword 1227
.hword 8957
.hword 8957
.hword 8957
.hword 8957
.hword 12078
.hword 12078
.hword 12078
.hword 12078
.hword 1029
.hword 1029
.hword 64081
.hword 64081
.hword 1212
.hword 1212
.hword 63929
.hword 63929
.hword 10129
.hword 10129
.hword 51214
.hword 51214
.hword 11930
.hword 11930
.hword 49718
.hword 49718
.hword 65317
.hword 65317
.hword 65317
.hword 65317
.hword 64681
.hword 64681
.hword 64681
.hword 64681
.hword 63380
.hword 63380
.hword 63380
.hword 63380
.hword 57120
.hword 57120
.hword 57120
.hword 57120
.hword 886
.hword 886
.hword 64982
.hword 64982
.hword 64357
.hword 64357
.hword 1143
.hword 1143
.hword 8721
.hword 8721
.hword 60083
.hword 60083
.hword 53931
.hword 53931
.hword 11251
.hword 11251
.hword 648
.hword 648
.hword 648
.hword 648
.hword 1481
.hword 1481
.hword 1481
.hword 1481
.hword 6378
.hword 6378
.hword 6378
.hword 6378
.hword 14578
.hword 14578
.hword 14578
.hword 14578
.hword 1026
.hword 1026
.hword 403
.hword 403
.hword 1092
.hword 1092
.hword 65011
.hword 65011
.hword 10099
.hword 10099
.hword 3967
.hword 3967
.hword 10749
.hword 10749
.hword 60368
.hword 60368
.hword 64824
.hword 64824
.hword 64824
.hword 64824
.hword 64854
.hword 64854
.hword 64854
.hword 64854
.hword 58528
.hword 58528
.hword 58528
.hword 58528
.hword 58823
.hword 58823
.hword 58823
.hword 58823
.hword 64801
.hword 64801
.hword 64673
.hword 64673
.hword 561
.hword 561
.hword 64306
.hword 64306
.hword 58301
.hword 58301
.hword 57041
.hword 57041
.hword 5522
.hword 5522
.hword 53429
.hword 53429
.hword 64609
.hword 64609
.hword 64609
.hword 64609
.hword 1534
.hword 1534
.hword 1534
.hword 1534
.hword 56411
.hword 56411
.hword 56411
.hword 56411
.hword 15099
.hword 15099
.hword 15099
.hword 15099
.hword 757
.hword 757
.hword 64980
.hword 64980
.hword 319
.hword 319
.hword 1063
.hword 1063
.hword 7451
.hword 7451
.hword 60063
.hword 60063
.hword 3140
.hword 3140
.hword 10463
.hword 10463
.hword 65075
.hword 65075
.hword 65075
.hword 65075
.hword 1438
.hword 1438
.hword 1438
.hword 1438
.hword 60998
.hword 60998
.hword 60998
.hword 60998
.hword 14155
.hword 14155
.hword 14155
.hword 14155
.hword 1645
.hword 1645
.hword 64297
.hword 64297
.hword 64756
.hword 64756
.hword 375
.hword 375
.hword 16192
.hword 16192
.hword 53340
.hword 53340
.hword 57858
.hword 57858
.hword 3691
.hword 3691
.hword 452
.hword 452
.hword 452
.hword 452
.hword 807
.hword 807
.hword 807
.hword 807
.hword 4449
.hword 4449
.hword 4449
.hword 4449
.hword 7943
.hword 7943
.hword 7943
.hword 7943
.hword 65427
.hword 65427
.hword 64244
.hword 64244
.hword 64505
.hword 64505
.hword 1584
.hword 1584
.hword 64463
.hword 64463
.hword 52819
.hword 52819
.hword 55388
.hword 55388
.hword 15592
.hword 15592
.hword 1435
.hword 1435
.hword 1435
.hword 1435
.hword 64526
.hword 64526
.hword 64526
.hword 64526
.hword 14125
.hword 14125
.hword 14125
.hword 14125
.hword 55594
.hword 55594
.hword 55594
.hword 55594
.hword 641
.hword 641
.hword 268
.hword 268
.hword 64544
.hword 64544
.hword 733
.hword 733
.hword 6309
.hword 6309
.hword 2638
.hword 2638
.hword 55772
.hword 55772
.hword 7215
.hword 7215
.hword 64122
.hword 64122
.hword 64122
.hword 64122
.hword 1320
.hword 1320
.hword 1320
.hword 1320
.hword 51618
.hword 51618
.hword 51618
.hword 51618
.hword 12993
.hword 12993
.hword 12993
.hword 12993
.hword 64595
.hword 64595
.hword 64644
.hword 64644
.hword 64515
.hword 64515
.hword 939
.hword 939
.hword 56274
.hword 56274
.hword 56756
.hword 56756
.hword 55486
.hword 55486
.hword 9243
.hword 9243
.hword 33
.hword 33
.hword 33
.hword 33
.hword 65072
.hword 65072
.hword 65072
.hword 65072
.hword 325
.hword 325
.hword 325
.hword 325
.hword 60969
.hword 60969
.hword 60969
.hword 60969
.hword 64894
.hword 64894
.hword 1461
.hword 1461
.hword 952
.hword 952
.hword 64054
.hword 64054
.hword 59217
.hword 59217
.hword 14381
.hword 14381
.hword 9371
.hword 9371
.hword 50948
.hword 50948
.hword 632
.hword 632
.hword 632
.hword 632
.hword 64720
.hword 64720
.hword 64720
.hword 64720
.hword 6221
.hword 6221
.hword 6221
.hword 6221
.hword 57504
.hword 57504
.hword 57504
.hword 57504
.hword 63996
.hword 63996
.hword 64996
.hword 64996
.hword 1651
.hword 1651
.hword 63910
.hword 63910
.hword 50377
.hword 50377
.hword 60221
.hword 60221
.hword 16251
.hword 16251
.hword 49531
.hword 49531
.hword 64184
.hword 64184
.hword 64184
.hword 64184
.hword 650
.hword 650
.hword 650
.hword 650
.hword 52228
.hword 52228
.hword 52228
.hword 52228
.hword 6398
.hword 6398
.hword 6398
.hword 6398
.hword 65257
.hword 65257
.hword 65222
.hword 65222
.hword 64363
.hword 64363
.hword 756
.hword 756
.hword 62790
.hword 62790
.hword 62445
.hword 62445
.hword 53990
.hword 53990
.hword 7441
.hword 7441
.hword 64262
.hword 64262
.hword 64262
.hword 64262
.hword 64484
.hword 64484
.hword 64484
.hword 64484
.hword 52996
.hword 52996
.hword 52996
.hword 52996
.hword 55181
.hword 55181
.hword 55181
.hword 55181
.hword 233
.hword 233
.hword 65488
.hword 65488
.hword 64869
.hword 64869
.hword 1409
.hword 1409
.hword 2293
.hword 2293
.hword 65064
.hword 65064
.hword 58971
.hword 58971
.hword 13869
.hword 13869
.hword 64511
.hword 64511
.hword 64511
.hword 64511
.hword 1197
.hword 1197
.hword 1197
.hword 1197
.hword 55447
.hword 55447
.hword 55447
.hword 55447
.hword 11782
.hword 11782
.hword 11782
.hword 11782
.hword 1100
.hword 1100
.hword 64495
.hword 64495
.hword 723
.hword 723
.hword 1637
.hword 1637
.hword 10828
.hword 10828
.hword 55289
.hword 55289
.hword 7117
.hword 7117
.hword 16113
.hword 16113
.hword 63963
.hword 63963
.hword 63963
.hword 63963
.hword 65460
.hword 65460
.hword 65460
.hword 65460
.hword 50053
.hword 50053
.hword 50053
.hword 50053
.hword 64788
.hword 64788
.hword 64788
.hword 64788
.hword 64856
.hword 64856
.hword 583
.hword 583
.hword 64968
.hword 64968
.hword 17
.hword 17
.hword 58843
.hword 58843
.hword 5739
.hword 5739
.hword 59945
.hword 59945
.hword 167
.hword 167
.hword 331
.hword 331
.hword 331
.hword 331
.hword 289
.hword 289
.hword 289
.hword 289
.hword 3258
.hword 3258
.hword 3258
.hword 3258
.hword 2845
.hword 2845
.hword 2845
.hword 2845
.hword 64556
.hword 55890
.hword 41
.hword 404
.hword 1640
.hword 16143
.hword 64788
.hword 58173
.hword 802
.hword 7894
.hword 64001
.hword 50427
.hword 64058
.hword 50988
.hword 1210
.hword 11910
.hword 65510
.hword 65280
.hword 65510
.hword 65280
.hword 65510
.hword 65280
.hword 65510
.hword 65280
.hword 26632
.hword 26632
.hword 0
.hword 0
.hword 0
.hword 0
.hword 0
.hword 0
.hword 3329
.hword 3329
.hword 3329
.hword 3329
.hword 3329
.hword 3329
.hword 3329
.hword 3329
.text

