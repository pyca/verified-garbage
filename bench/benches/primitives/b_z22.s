.text
.globl cr_fwd_z22
.p2align 4
cr_fwd_z22:
adrp x2, cr_fwd_z22_t
add x2, x2, :lo12:cr_fwd_z22_t
ldr q0, [x2, #0]
ldr q1, [x2, #16]
ldr q2, [x2, #32]
ldr q3, [x2, #48]
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
sqrdmulh v4.8h, v24.8h, v0.h[3]
sqrdmulh v6.8h, v25.8h, v0.h[3]
mul v5.8h, v24.8h, v0.h[2]
mul v7.8h, v25.8h, v0.h[2]
mls v5.8h, v4.8h, v0.h[0]
mls v7.8h, v6.8h, v0.h[0]
sub v4.8h, v16.8h, v5.8h
sub v6.8h, v17.8h, v7.8h
add v16.8h, v16.8h, v5.8h
add v17.8h, v17.8h, v7.8h
sqrdmulh v5.8h, v26.8h, v0.h[3]
sqrdmulh v7.8h, v27.8h, v0.h[3]
mul v24.8h, v26.8h, v0.h[2]
mul v25.8h, v27.8h, v0.h[2]
mls v24.8h, v5.8h, v0.h[0]
mls v25.8h, v7.8h, v0.h[0]
sub v5.8h, v18.8h, v24.8h
sub v7.8h, v19.8h, v25.8h
add v18.8h, v18.8h, v24.8h
add v19.8h, v19.8h, v25.8h
sqrdmulh v24.8h, v28.8h, v0.h[3]
sqrdmulh v25.8h, v29.8h, v0.h[3]
mul v26.8h, v28.8h, v0.h[2]
mul v27.8h, v29.8h, v0.h[2]
mls v26.8h, v24.8h, v0.h[0]
mls v27.8h, v25.8h, v0.h[0]
sub v24.8h, v20.8h, v26.8h
sub v25.8h, v21.8h, v27.8h
add v20.8h, v20.8h, v26.8h
add v21.8h, v21.8h, v27.8h
sqrdmulh v26.8h, v30.8h, v0.h[3]
sqrdmulh v27.8h, v31.8h, v0.h[3]
mul v28.8h, v30.8h, v0.h[2]
mul v29.8h, v31.8h, v0.h[2]
mls v28.8h, v26.8h, v0.h[0]
mls v29.8h, v27.8h, v0.h[0]
sub v26.8h, v22.8h, v28.8h
sub v27.8h, v23.8h, v29.8h
add v22.8h, v22.8h, v28.8h
add v23.8h, v23.8h, v29.8h
sqrdmulh v28.8h, v20.8h, v0.h[5]
sqrdmulh v29.8h, v21.8h, v0.h[5]
mul v30.8h, v20.8h, v0.h[4]
mul v31.8h, v21.8h, v0.h[4]
mls v30.8h, v28.8h, v0.h[0]
mls v31.8h, v29.8h, v0.h[0]
sub v28.8h, v16.8h, v30.8h
sub v29.8h, v17.8h, v31.8h
add v16.8h, v16.8h, v30.8h
add v17.8h, v17.8h, v31.8h
sqrdmulh v30.8h, v22.8h, v0.h[5]
sqrdmulh v31.8h, v23.8h, v0.h[5]
mul v20.8h, v22.8h, v0.h[4]
mul v21.8h, v23.8h, v0.h[4]
mls v20.8h, v30.8h, v0.h[0]
mls v21.8h, v31.8h, v0.h[0]
sub v30.8h, v18.8h, v20.8h
sub v31.8h, v19.8h, v21.8h
add v18.8h, v18.8h, v20.8h
add v19.8h, v19.8h, v21.8h
sqrdmulh v20.8h, v24.8h, v0.h[7]
sqrdmulh v21.8h, v25.8h, v0.h[7]
mul v22.8h, v24.8h, v0.h[6]
mul v23.8h, v25.8h, v0.h[6]
mls v22.8h, v20.8h, v0.h[0]
mls v23.8h, v21.8h, v0.h[0]
sub v20.8h, v4.8h, v22.8h
sub v21.8h, v6.8h, v23.8h
add v4.8h, v4.8h, v22.8h
add v6.8h, v6.8h, v23.8h
sqrdmulh v22.8h, v26.8h, v0.h[7]
sqrdmulh v23.8h, v27.8h, v0.h[7]
mul v24.8h, v26.8h, v0.h[6]
mul v25.8h, v27.8h, v0.h[6]
mls v24.8h, v22.8h, v0.h[0]
mls v25.8h, v23.8h, v0.h[0]
sub v22.8h, v5.8h, v24.8h
sub v23.8h, v7.8h, v25.8h
add v5.8h, v5.8h, v24.8h
add v7.8h, v7.8h, v25.8h
sqrdmulh v24.8h, v18.8h, v1.h[1]
sqrdmulh v25.8h, v19.8h, v1.h[1]
mul v26.8h, v18.8h, v1.h[0]
mul v27.8h, v19.8h, v1.h[0]
mls v26.8h, v24.8h, v0.h[0]
mls v27.8h, v25.8h, v0.h[0]
sub v24.8h, v16.8h, v26.8h
sub v25.8h, v17.8h, v27.8h
add v16.8h, v16.8h, v26.8h
add v17.8h, v17.8h, v27.8h
sqrdmulh v26.8h, v30.8h, v1.h[3]
sqrdmulh v27.8h, v31.8h, v1.h[3]
mul v18.8h, v30.8h, v1.h[2]
mul v19.8h, v31.8h, v1.h[2]
mls v18.8h, v26.8h, v0.h[0]
mls v19.8h, v27.8h, v0.h[0]
sub v26.8h, v28.8h, v18.8h
sub v27.8h, v29.8h, v19.8h
add v28.8h, v28.8h, v18.8h
add v29.8h, v29.8h, v19.8h
sqrdmulh v18.8h, v5.8h, v1.h[5]
sqrdmulh v19.8h, v7.8h, v1.h[5]
mul v30.8h, v5.8h, v1.h[4]
mul v31.8h, v7.8h, v1.h[4]
mls v30.8h, v18.8h, v0.h[0]
mls v31.8h, v19.8h, v0.h[0]
sub v18.8h, v4.8h, v30.8h
sub v19.8h, v6.8h, v31.8h
add v4.8h, v4.8h, v30.8h
add v6.8h, v6.8h, v31.8h
sqrdmulh v30.8h, v22.8h, v1.h[7]
sqrdmulh v31.8h, v23.8h, v1.h[7]
mul v5.8h, v22.8h, v1.h[6]
mul v7.8h, v23.8h, v1.h[6]
mls v5.8h, v30.8h, v0.h[0]
mls v7.8h, v31.8h, v0.h[0]
sub v30.8h, v20.8h, v5.8h
sub v31.8h, v21.8h, v7.8h
add v20.8h, v20.8h, v5.8h
add v21.8h, v21.8h, v7.8h
sqrdmulh v5.8h, v17.8h, v2.h[1]
sqrdmulh v7.8h, v25.8h, v2.h[3]
mul v22.8h, v17.8h, v2.h[0]
mul v23.8h, v25.8h, v2.h[2]
mls v22.8h, v5.8h, v0.h[0]
mls v23.8h, v7.8h, v0.h[0]
sub v5.8h, v16.8h, v22.8h
sub v7.8h, v24.8h, v23.8h
add v16.8h, v16.8h, v22.8h
add v24.8h, v24.8h, v23.8h
sqrdmulh v22.8h, v29.8h, v2.h[5]
sqrdmulh v23.8h, v27.8h, v2.h[7]
mul v17.8h, v29.8h, v2.h[4]
mul v25.8h, v27.8h, v2.h[6]
mls v17.8h, v22.8h, v0.h[0]
mls v25.8h, v23.8h, v0.h[0]
sub v22.8h, v28.8h, v17.8h
sub v23.8h, v26.8h, v25.8h
add v28.8h, v28.8h, v17.8h
add v26.8h, v26.8h, v25.8h
sqrdmulh v17.8h, v6.8h, v3.h[1]
sqrdmulh v25.8h, v19.8h, v3.h[3]
mul v29.8h, v6.8h, v3.h[0]
mul v27.8h, v19.8h, v3.h[2]
mls v29.8h, v17.8h, v0.h[0]
mls v27.8h, v25.8h, v0.h[0]
sub v17.8h, v4.8h, v29.8h
sub v25.8h, v18.8h, v27.8h
add v4.8h, v4.8h, v29.8h
add v18.8h, v18.8h, v27.8h
sqrdmulh v29.8h, v21.8h, v3.h[5]
sqrdmulh v27.8h, v31.8h, v3.h[7]
mul v6.8h, v21.8h, v3.h[4]
mul v19.8h, v31.8h, v3.h[6]
mls v6.8h, v29.8h, v0.h[0]
mls v19.8h, v27.8h, v0.h[0]
sub v29.8h, v20.8h, v6.8h
sub v27.8h, v30.8h, v19.8h
add v20.8h, v20.8h, v6.8h
add v30.8h, v30.8h, v19.8h
str q16, [x0, #0]
str q5, [x0, #32]
str q24, [x0, #64]
str q7, [x0, #96]
str q28, [x0, #128]
str q22, [x0, #160]
str q26, [x0, #192]
str q23, [x0, #224]
str q4, [x0, #256]
str q17, [x0, #288]
str q18, [x0, #320]
str q25, [x0, #352]
str q20, [x0, #384]
str q29, [x0, #416]
str q30, [x0, #448]
str q27, [x0, #480]
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
sqrdmulh v4.8h, v24.8h, v0.h[3]
sqrdmulh v6.8h, v25.8h, v0.h[3]
mul v5.8h, v24.8h, v0.h[2]
mul v7.8h, v25.8h, v0.h[2]
mls v5.8h, v4.8h, v0.h[0]
mls v7.8h, v6.8h, v0.h[0]
sub v4.8h, v16.8h, v5.8h
sub v6.8h, v17.8h, v7.8h
add v16.8h, v16.8h, v5.8h
add v17.8h, v17.8h, v7.8h
sqrdmulh v5.8h, v26.8h, v0.h[3]
sqrdmulh v7.8h, v27.8h, v0.h[3]
mul v24.8h, v26.8h, v0.h[2]
mul v25.8h, v27.8h, v0.h[2]
mls v24.8h, v5.8h, v0.h[0]
mls v25.8h, v7.8h, v0.h[0]
sub v5.8h, v18.8h, v24.8h
sub v7.8h, v19.8h, v25.8h
add v18.8h, v18.8h, v24.8h
add v19.8h, v19.8h, v25.8h
sqrdmulh v24.8h, v28.8h, v0.h[3]
sqrdmulh v25.8h, v29.8h, v0.h[3]
mul v26.8h, v28.8h, v0.h[2]
mul v27.8h, v29.8h, v0.h[2]
mls v26.8h, v24.8h, v0.h[0]
mls v27.8h, v25.8h, v0.h[0]
sub v24.8h, v20.8h, v26.8h
sub v25.8h, v21.8h, v27.8h
add v20.8h, v20.8h, v26.8h
add v21.8h, v21.8h, v27.8h
sqrdmulh v26.8h, v30.8h, v0.h[3]
sqrdmulh v27.8h, v31.8h, v0.h[3]
mul v28.8h, v30.8h, v0.h[2]
mul v29.8h, v31.8h, v0.h[2]
mls v28.8h, v26.8h, v0.h[0]
mls v29.8h, v27.8h, v0.h[0]
sub v26.8h, v22.8h, v28.8h
sub v27.8h, v23.8h, v29.8h
add v22.8h, v22.8h, v28.8h
add v23.8h, v23.8h, v29.8h
sqrdmulh v28.8h, v20.8h, v0.h[5]
sqrdmulh v29.8h, v21.8h, v0.h[5]
mul v30.8h, v20.8h, v0.h[4]
mul v31.8h, v21.8h, v0.h[4]
mls v30.8h, v28.8h, v0.h[0]
mls v31.8h, v29.8h, v0.h[0]
sub v28.8h, v16.8h, v30.8h
sub v29.8h, v17.8h, v31.8h
add v16.8h, v16.8h, v30.8h
add v17.8h, v17.8h, v31.8h
sqrdmulh v30.8h, v22.8h, v0.h[5]
sqrdmulh v31.8h, v23.8h, v0.h[5]
mul v20.8h, v22.8h, v0.h[4]
mul v21.8h, v23.8h, v0.h[4]
mls v20.8h, v30.8h, v0.h[0]
mls v21.8h, v31.8h, v0.h[0]
sub v30.8h, v18.8h, v20.8h
sub v31.8h, v19.8h, v21.8h
add v18.8h, v18.8h, v20.8h
add v19.8h, v19.8h, v21.8h
sqrdmulh v20.8h, v24.8h, v0.h[7]
sqrdmulh v21.8h, v25.8h, v0.h[7]
mul v22.8h, v24.8h, v0.h[6]
mul v23.8h, v25.8h, v0.h[6]
mls v22.8h, v20.8h, v0.h[0]
mls v23.8h, v21.8h, v0.h[0]
sub v20.8h, v4.8h, v22.8h
sub v21.8h, v6.8h, v23.8h
add v4.8h, v4.8h, v22.8h
add v6.8h, v6.8h, v23.8h
sqrdmulh v22.8h, v26.8h, v0.h[7]
sqrdmulh v23.8h, v27.8h, v0.h[7]
mul v24.8h, v26.8h, v0.h[6]
mul v25.8h, v27.8h, v0.h[6]
mls v24.8h, v22.8h, v0.h[0]
mls v25.8h, v23.8h, v0.h[0]
sub v22.8h, v5.8h, v24.8h
sub v23.8h, v7.8h, v25.8h
add v5.8h, v5.8h, v24.8h
add v7.8h, v7.8h, v25.8h
sqrdmulh v24.8h, v18.8h, v1.h[1]
sqrdmulh v25.8h, v19.8h, v1.h[1]
mul v26.8h, v18.8h, v1.h[0]
mul v27.8h, v19.8h, v1.h[0]
mls v26.8h, v24.8h, v0.h[0]
mls v27.8h, v25.8h, v0.h[0]
sub v24.8h, v16.8h, v26.8h
sub v25.8h, v17.8h, v27.8h
add v16.8h, v16.8h, v26.8h
add v17.8h, v17.8h, v27.8h
sqrdmulh v26.8h, v30.8h, v1.h[3]
sqrdmulh v27.8h, v31.8h, v1.h[3]
mul v18.8h, v30.8h, v1.h[2]
mul v19.8h, v31.8h, v1.h[2]
mls v18.8h, v26.8h, v0.h[0]
mls v19.8h, v27.8h, v0.h[0]
sub v26.8h, v28.8h, v18.8h
sub v27.8h, v29.8h, v19.8h
add v28.8h, v28.8h, v18.8h
add v29.8h, v29.8h, v19.8h
sqrdmulh v18.8h, v5.8h, v1.h[5]
sqrdmulh v19.8h, v7.8h, v1.h[5]
mul v30.8h, v5.8h, v1.h[4]
mul v31.8h, v7.8h, v1.h[4]
mls v30.8h, v18.8h, v0.h[0]
mls v31.8h, v19.8h, v0.h[0]
sub v18.8h, v4.8h, v30.8h
sub v19.8h, v6.8h, v31.8h
add v4.8h, v4.8h, v30.8h
add v6.8h, v6.8h, v31.8h
sqrdmulh v30.8h, v22.8h, v1.h[7]
sqrdmulh v31.8h, v23.8h, v1.h[7]
mul v5.8h, v22.8h, v1.h[6]
mul v7.8h, v23.8h, v1.h[6]
mls v5.8h, v30.8h, v0.h[0]
mls v7.8h, v31.8h, v0.h[0]
sub v30.8h, v20.8h, v5.8h
sub v31.8h, v21.8h, v7.8h
add v20.8h, v20.8h, v5.8h
add v21.8h, v21.8h, v7.8h
sqrdmulh v5.8h, v17.8h, v2.h[1]
sqrdmulh v7.8h, v25.8h, v2.h[3]
mul v22.8h, v17.8h, v2.h[0]
mul v23.8h, v25.8h, v2.h[2]
mls v22.8h, v5.8h, v0.h[0]
mls v23.8h, v7.8h, v0.h[0]
sub v5.8h, v16.8h, v22.8h
sub v7.8h, v24.8h, v23.8h
add v16.8h, v16.8h, v22.8h
add v24.8h, v24.8h, v23.8h
sqrdmulh v22.8h, v29.8h, v2.h[5]
sqrdmulh v23.8h, v27.8h, v2.h[7]
mul v17.8h, v29.8h, v2.h[4]
mul v25.8h, v27.8h, v2.h[6]
mls v17.8h, v22.8h, v0.h[0]
mls v25.8h, v23.8h, v0.h[0]
sub v22.8h, v28.8h, v17.8h
sub v23.8h, v26.8h, v25.8h
add v28.8h, v28.8h, v17.8h
add v26.8h, v26.8h, v25.8h
sqrdmulh v17.8h, v6.8h, v3.h[1]
sqrdmulh v25.8h, v19.8h, v3.h[3]
mul v29.8h, v6.8h, v3.h[0]
mul v27.8h, v19.8h, v3.h[2]
mls v29.8h, v17.8h, v0.h[0]
mls v27.8h, v25.8h, v0.h[0]
sub v17.8h, v4.8h, v29.8h
sub v25.8h, v18.8h, v27.8h
add v4.8h, v4.8h, v29.8h
add v18.8h, v18.8h, v27.8h
sqrdmulh v29.8h, v21.8h, v3.h[5]
sqrdmulh v27.8h, v31.8h, v3.h[7]
mul v6.8h, v21.8h, v3.h[4]
mul v19.8h, v31.8h, v3.h[6]
mls v6.8h, v29.8h, v0.h[0]
mls v19.8h, v27.8h, v0.h[0]
sub v29.8h, v20.8h, v6.8h
sub v27.8h, v30.8h, v19.8h
add v20.8h, v20.8h, v6.8h
add v30.8h, v30.8h, v19.8h
str q16, [x0, #16]
str q5, [x0, #48]
str q24, [x0, #80]
str q7, [x0, #112]
str q28, [x0, #144]
str q22, [x0, #176]
str q26, [x0, #208]
str q23, [x0, #240]
str q4, [x0, #272]
str q17, [x0, #304]
str q18, [x0, #336]
str q25, [x0, #368]
str q20, [x0, #400]
str q29, [x0, #432]
str q30, [x0, #464]
str q27, [x0, #496]
ldr q0, [x2, #64]
ldr q1, [x2, #80]
ldr q2, [x2, #96]
ldr q3, [x2, #112]
ldr q7, [x2, #128]
ldr q16, [x0, #0]
ldr q22, [x0, #32]
ldr q17, [x0, #16]
ldr q23, [x0, #48]
sqrdmulh v18.8h, v17.8h, v0.h[1]
sqrdmulh v24.8h, v23.8h, v0.h[3]
mul v19.8h, v17.8h, v0.h[0]
mul v25.8h, v23.8h, v0.h[2]
mls v19.8h, v18.8h, v7.h[0]
mls v25.8h, v24.8h, v7.h[0]
sub v17.8h, v16.8h, v19.8h
sub v23.8h, v22.8h, v25.8h
add v16.8h, v16.8h, v19.8h
add v22.8h, v22.8h, v25.8h
trn1 v18.2d, v16.2d, v17.2d
trn1 v24.2d, v22.2d, v23.2d
trn2 v19.2d, v16.2d, v17.2d
trn2 v25.2d, v22.2d, v23.2d
ldr q20, [x2, #144]
ldr q26, [x2, #208]
ldr q21, [x2, #160]
ldr q27, [x2, #224]
sqrdmulh v16.8h, v19.8h, v21.8h
sqrdmulh v22.8h, v25.8h, v27.8h
mul v17.8h, v19.8h, v20.8h
mul v23.8h, v25.8h, v26.8h
mls v17.8h, v16.8h, v7.h[0]
mls v23.8h, v22.8h, v7.h[0]
sub v19.8h, v18.8h, v17.8h
sub v25.8h, v24.8h, v23.8h
add v18.8h, v18.8h, v17.8h
add v24.8h, v24.8h, v23.8h
trn1 v16.4s, v18.4s, v19.4s
trn1 v22.4s, v24.4s, v25.4s
trn2 v17.4s, v18.4s, v19.4s
trn2 v23.4s, v24.4s, v25.4s
ldr q20, [x2, #176]
ldr q26, [x2, #240]
ldr q21, [x2, #192]
ldr q27, [x2, #256]
sqrdmulh v18.8h, v17.8h, v21.8h
sqrdmulh v24.8h, v23.8h, v27.8h
mul v19.8h, v17.8h, v20.8h
mul v25.8h, v23.8h, v26.8h
mls v19.8h, v18.8h, v7.h[0]
mls v25.8h, v24.8h, v7.h[0]
sub v17.8h, v16.8h, v19.8h
sub v23.8h, v22.8h, v25.8h
add v16.8h, v16.8h, v19.8h
add v22.8h, v22.8h, v25.8h
sqrdmulh v18.8h, v16.8h, v7.h[1]
sqrdmulh v24.8h, v22.8h, v7.h[1]
sqrdmulh v19.8h, v17.8h, v7.h[1]
sqrdmulh v25.8h, v23.8h, v7.h[1]
sshr v18.8h, v18.8h, #11
sshr v24.8h, v24.8h, #11
sshr v19.8h, v19.8h, #11
sshr v25.8h, v25.8h, #11
mls v16.8h, v18.8h, v7.h[0]
mls v22.8h, v24.8h, v7.h[0]
mls v17.8h, v19.8h, v7.h[0]
mls v23.8h, v25.8h, v7.h[0]
zip1 v18.4s, v16.4s, v17.4s
zip1 v24.4s, v22.4s, v23.4s
zip2 v19.4s, v16.4s, v17.4s
zip2 v25.4s, v22.4s, v23.4s
str q18, [x0, #0]
str q24, [x0, #32]
str q19, [x0, #16]
str q25, [x0, #48]
ldr q28, [x0, #64]
ldr q6, [x0, #96]
ldr q29, [x0, #80]
ldr q16, [x0, #112]
sqrdmulh v30.8h, v29.8h, v0.h[5]
sqrdmulh v17.8h, v16.8h, v0.h[7]
mul v31.8h, v29.8h, v0.h[4]
mul v18.8h, v16.8h, v0.h[6]
mls v31.8h, v30.8h, v7.h[0]
mls v18.8h, v17.8h, v7.h[0]
sub v29.8h, v28.8h, v31.8h
sub v16.8h, v6.8h, v18.8h
add v28.8h, v28.8h, v31.8h
add v6.8h, v6.8h, v18.8h
trn1 v30.2d, v28.2d, v29.2d
trn1 v17.2d, v6.2d, v16.2d
trn2 v31.2d, v28.2d, v29.2d
trn2 v18.2d, v6.2d, v16.2d
ldr q4, [x2, #272]
ldr q19, [x2, #336]
ldr q5, [x2, #288]
ldr q20, [x2, #352]
sqrdmulh v28.8h, v31.8h, v5.8h
sqrdmulh v6.8h, v18.8h, v20.8h
mul v29.8h, v31.8h, v4.8h
mul v16.8h, v18.8h, v19.8h
mls v29.8h, v28.8h, v7.h[0]
mls v16.8h, v6.8h, v7.h[0]
sub v31.8h, v30.8h, v29.8h
sub v18.8h, v17.8h, v16.8h
add v30.8h, v30.8h, v29.8h
add v17.8h, v17.8h, v16.8h
trn1 v28.4s, v30.4s, v31.4s
trn1 v6.4s, v17.4s, v18.4s
trn2 v29.4s, v30.4s, v31.4s
trn2 v16.4s, v17.4s, v18.4s
ldr q4, [x2, #304]
ldr q19, [x2, #368]
ldr q5, [x2, #320]
ldr q20, [x2, #384]
sqrdmulh v30.8h, v29.8h, v5.8h
sqrdmulh v17.8h, v16.8h, v20.8h
mul v31.8h, v29.8h, v4.8h
mul v18.8h, v16.8h, v19.8h
mls v31.8h, v30.8h, v7.h[0]
mls v18.8h, v17.8h, v7.h[0]
sub v29.8h, v28.8h, v31.8h
sub v16.8h, v6.8h, v18.8h
add v28.8h, v28.8h, v31.8h
add v6.8h, v6.8h, v18.8h
sqrdmulh v30.8h, v28.8h, v7.h[1]
sqrdmulh v17.8h, v6.8h, v7.h[1]
sqrdmulh v31.8h, v29.8h, v7.h[1]
sqrdmulh v18.8h, v16.8h, v7.h[1]
sshr v30.8h, v30.8h, #11
sshr v17.8h, v17.8h, #11
sshr v31.8h, v31.8h, #11
sshr v18.8h, v18.8h, #11
mls v28.8h, v30.8h, v7.h[0]
mls v6.8h, v17.8h, v7.h[0]
mls v29.8h, v31.8h, v7.h[0]
mls v16.8h, v18.8h, v7.h[0]
zip1 v30.4s, v28.4s, v29.4s
zip1 v17.4s, v6.4s, v16.4s
zip2 v31.4s, v28.4s, v29.4s
zip2 v18.4s, v6.4s, v16.4s
str q30, [x0, #64]
str q17, [x0, #96]
str q31, [x0, #80]
str q18, [x0, #112]
ldr q21, [x0, #128]
ldr q27, [x0, #160]
ldr q22, [x0, #144]
ldr q28, [x0, #176]
sqrdmulh v23.8h, v22.8h, v1.h[1]
sqrdmulh v29.8h, v28.8h, v1.h[3]
mul v24.8h, v22.8h, v1.h[0]
mul v30.8h, v28.8h, v1.h[2]
mls v24.8h, v23.8h, v7.h[0]
mls v30.8h, v29.8h, v7.h[0]
sub v22.8h, v21.8h, v24.8h
sub v28.8h, v27.8h, v30.8h
add v21.8h, v21.8h, v24.8h
add v27.8h, v27.8h, v30.8h
trn1 v23.2d, v21.2d, v22.2d
trn1 v29.2d, v27.2d, v28.2d
trn2 v24.2d, v21.2d, v22.2d
trn2 v30.2d, v27.2d, v28.2d
ldr q25, [x2, #400]
ldr q31, [x2, #464]
ldr q26, [x2, #416]
ldr q4, [x2, #480]
sqrdmulh v21.8h, v24.8h, v26.8h
sqrdmulh v27.8h, v30.8h, v4.8h
mul v22.8h, v24.8h, v25.8h
mul v28.8h, v30.8h, v31.8h
mls v22.8h, v21.8h, v7.h[0]
mls v28.8h, v27.8h, v7.h[0]
sub v24.8h, v23.8h, v22.8h
sub v30.8h, v29.8h, v28.8h
add v23.8h, v23.8h, v22.8h
add v29.8h, v29.8h, v28.8h
trn1 v21.4s, v23.4s, v24.4s
trn1 v27.4s, v29.4s, v30.4s
trn2 v22.4s, v23.4s, v24.4s
trn2 v28.4s, v29.4s, v30.4s
ldr q25, [x2, #432]
ldr q31, [x2, #496]
ldr q26, [x2, #448]
ldr q4, [x2, #512]
sqrdmulh v23.8h, v22.8h, v26.8h
sqrdmulh v29.8h, v28.8h, v4.8h
mul v24.8h, v22.8h, v25.8h
mul v30.8h, v28.8h, v31.8h
mls v24.8h, v23.8h, v7.h[0]
mls v30.8h, v29.8h, v7.h[0]
sub v22.8h, v21.8h, v24.8h
sub v28.8h, v27.8h, v30.8h
add v21.8h, v21.8h, v24.8h
add v27.8h, v27.8h, v30.8h
sqrdmulh v23.8h, v21.8h, v7.h[1]
sqrdmulh v29.8h, v27.8h, v7.h[1]
sqrdmulh v24.8h, v22.8h, v7.h[1]
sqrdmulh v30.8h, v28.8h, v7.h[1]
sshr v23.8h, v23.8h, #11
sshr v29.8h, v29.8h, #11
sshr v24.8h, v24.8h, #11
sshr v30.8h, v30.8h, #11
mls v21.8h, v23.8h, v7.h[0]
mls v27.8h, v29.8h, v7.h[0]
mls v22.8h, v24.8h, v7.h[0]
mls v28.8h, v30.8h, v7.h[0]
zip1 v23.4s, v21.4s, v22.4s
zip1 v29.4s, v27.4s, v28.4s
zip2 v24.4s, v21.4s, v22.4s
zip2 v30.4s, v27.4s, v28.4s
str q23, [x0, #128]
str q29, [x0, #160]
str q24, [x0, #144]
str q30, [x0, #176]
ldr q5, [x0, #192]
ldr q20, [x0, #224]
ldr q6, [x0, #208]
ldr q21, [x0, #240]
sqrdmulh v16.8h, v6.8h, v1.h[5]
sqrdmulh v22.8h, v21.8h, v1.h[7]
mul v17.8h, v6.8h, v1.h[4]
mul v23.8h, v21.8h, v1.h[6]
mls v17.8h, v16.8h, v7.h[0]
mls v23.8h, v22.8h, v7.h[0]
sub v6.8h, v5.8h, v17.8h
sub v21.8h, v20.8h, v23.8h
add v5.8h, v5.8h, v17.8h
add v20.8h, v20.8h, v23.8h
trn1 v16.2d, v5.2d, v6.2d
trn1 v22.2d, v20.2d, v21.2d
trn2 v17.2d, v5.2d, v6.2d
trn2 v23.2d, v20.2d, v21.2d
ldr q18, [x2, #528]
ldr q24, [x2, #592]
ldr q19, [x2, #544]
ldr q25, [x2, #608]
sqrdmulh v5.8h, v17.8h, v19.8h
sqrdmulh v20.8h, v23.8h, v25.8h
mul v6.8h, v17.8h, v18.8h
mul v21.8h, v23.8h, v24.8h
mls v6.8h, v5.8h, v7.h[0]
mls v21.8h, v20.8h, v7.h[0]
sub v17.8h, v16.8h, v6.8h
sub v23.8h, v22.8h, v21.8h
add v16.8h, v16.8h, v6.8h
add v22.8h, v22.8h, v21.8h
trn1 v5.4s, v16.4s, v17.4s
trn1 v20.4s, v22.4s, v23.4s
trn2 v6.4s, v16.4s, v17.4s
trn2 v21.4s, v22.4s, v23.4s
ldr q18, [x2, #560]
ldr q24, [x2, #624]
ldr q19, [x2, #576]
ldr q25, [x2, #640]
sqrdmulh v16.8h, v6.8h, v19.8h
sqrdmulh v22.8h, v21.8h, v25.8h
mul v17.8h, v6.8h, v18.8h
mul v23.8h, v21.8h, v24.8h
mls v17.8h, v16.8h, v7.h[0]
mls v23.8h, v22.8h, v7.h[0]
sub v6.8h, v5.8h, v17.8h
sub v21.8h, v20.8h, v23.8h
add v5.8h, v5.8h, v17.8h
add v20.8h, v20.8h, v23.8h
sqrdmulh v16.8h, v5.8h, v7.h[1]
sqrdmulh v22.8h, v20.8h, v7.h[1]
sqrdmulh v17.8h, v6.8h, v7.h[1]
sqrdmulh v23.8h, v21.8h, v7.h[1]
sshr v16.8h, v16.8h, #11
sshr v22.8h, v22.8h, #11
sshr v17.8h, v17.8h, #11
sshr v23.8h, v23.8h, #11
mls v5.8h, v16.8h, v7.h[0]
mls v20.8h, v22.8h, v7.h[0]
mls v6.8h, v17.8h, v7.h[0]
mls v21.8h, v23.8h, v7.h[0]
zip1 v16.4s, v5.4s, v6.4s
zip1 v22.4s, v20.4s, v21.4s
zip2 v17.4s, v5.4s, v6.4s
zip2 v23.4s, v20.4s, v21.4s
str q16, [x0, #192]
str q22, [x0, #224]
str q17, [x0, #208]
str q23, [x0, #240]
ldr q26, [x0, #256]
ldr q4, [x0, #288]
ldr q27, [x0, #272]
ldr q5, [x0, #304]
sqrdmulh v28.8h, v27.8h, v2.h[1]
sqrdmulh v6.8h, v5.8h, v2.h[3]
mul v29.8h, v27.8h, v2.h[0]
mul v16.8h, v5.8h, v2.h[2]
mls v29.8h, v28.8h, v7.h[0]
mls v16.8h, v6.8h, v7.h[0]
sub v27.8h, v26.8h, v29.8h
sub v5.8h, v4.8h, v16.8h
add v26.8h, v26.8h, v29.8h
add v4.8h, v4.8h, v16.8h
trn1 v28.2d, v26.2d, v27.2d
trn1 v6.2d, v4.2d, v5.2d
trn2 v29.2d, v26.2d, v27.2d
trn2 v16.2d, v4.2d, v5.2d
ldr q30, [x2, #656]
ldr q17, [x2, #720]
ldr q31, [x2, #672]
ldr q18, [x2, #736]
sqrdmulh v26.8h, v29.8h, v31.8h
sqrdmulh v4.8h, v16.8h, v18.8h
mul v27.8h, v29.8h, v30.8h
mul v5.8h, v16.8h, v17.8h
mls v27.8h, v26.8h, v7.h[0]
mls v5.8h, v4.8h, v7.h[0]
sub v29.8h, v28.8h, v27.8h
sub v16.8h, v6.8h, v5.8h
add v28.8h, v28.8h, v27.8h
add v6.8h, v6.8h, v5.8h
trn1 v26.4s, v28.4s, v29.4s
trn1 v4.4s, v6.4s, v16.4s
trn2 v27.4s, v28.4s, v29.4s
trn2 v5.4s, v6.4s, v16.4s
ldr q30, [x2, #688]
ldr q17, [x2, #752]
ldr q31, [x2, #704]
ldr q18, [x2, #768]
sqrdmulh v28.8h, v27.8h, v31.8h
sqrdmulh v6.8h, v5.8h, v18.8h
mul v29.8h, v27.8h, v30.8h
mul v16.8h, v5.8h, v17.8h
mls v29.8h, v28.8h, v7.h[0]
mls v16.8h, v6.8h, v7.h[0]
sub v27.8h, v26.8h, v29.8h
sub v5.8h, v4.8h, v16.8h
add v26.8h, v26.8h, v29.8h
add v4.8h, v4.8h, v16.8h
sqrdmulh v28.8h, v26.8h, v7.h[1]
sqrdmulh v6.8h, v4.8h, v7.h[1]
sqrdmulh v29.8h, v27.8h, v7.h[1]
sqrdmulh v16.8h, v5.8h, v7.h[1]
sshr v28.8h, v28.8h, #11
sshr v6.8h, v6.8h, #11
sshr v29.8h, v29.8h, #11
sshr v16.8h, v16.8h, #11
mls v26.8h, v28.8h, v7.h[0]
mls v4.8h, v6.8h, v7.h[0]
mls v27.8h, v29.8h, v7.h[0]
mls v5.8h, v16.8h, v7.h[0]
zip1 v28.4s, v26.4s, v27.4s
zip1 v6.4s, v4.4s, v5.4s
zip2 v29.4s, v26.4s, v27.4s
zip2 v16.4s, v4.4s, v5.4s
str q28, [x0, #256]
str q6, [x0, #288]
str q29, [x0, #272]
str q16, [x0, #304]
ldr q19, [x0, #320]
ldr q25, [x0, #352]
ldr q20, [x0, #336]
ldr q26, [x0, #368]
sqrdmulh v21.8h, v20.8h, v2.h[5]
sqrdmulh v27.8h, v26.8h, v2.h[7]
mul v22.8h, v20.8h, v2.h[4]
mul v28.8h, v26.8h, v2.h[6]
mls v22.8h, v21.8h, v7.h[0]
mls v28.8h, v27.8h, v7.h[0]
sub v20.8h, v19.8h, v22.8h
sub v26.8h, v25.8h, v28.8h
add v19.8h, v19.8h, v22.8h
add v25.8h, v25.8h, v28.8h
trn1 v21.2d, v19.2d, v20.2d
trn1 v27.2d, v25.2d, v26.2d
trn2 v22.2d, v19.2d, v20.2d
trn2 v28.2d, v25.2d, v26.2d
ldr q23, [x2, #784]
ldr q29, [x2, #848]
ldr q24, [x2, #800]
ldr q30, [x2, #864]
sqrdmulh v19.8h, v22.8h, v24.8h
sqrdmulh v25.8h, v28.8h, v30.8h
mul v20.8h, v22.8h, v23.8h
mul v26.8h, v28.8h, v29.8h
mls v20.8h, v19.8h, v7.h[0]
mls v26.8h, v25.8h, v7.h[0]
sub v22.8h, v21.8h, v20.8h
sub v28.8h, v27.8h, v26.8h
add v21.8h, v21.8h, v20.8h
add v27.8h, v27.8h, v26.8h
trn1 v19.4s, v21.4s, v22.4s
trn1 v25.4s, v27.4s, v28.4s
trn2 v20.4s, v21.4s, v22.4s
trn2 v26.4s, v27.4s, v28.4s
ldr q23, [x2, #816]
ldr q29, [x2, #880]
ldr q24, [x2, #832]
ldr q30, [x2, #896]
sqrdmulh v21.8h, v20.8h, v24.8h
sqrdmulh v27.8h, v26.8h, v30.8h
mul v22.8h, v20.8h, v23.8h
mul v28.8h, v26.8h, v29.8h
mls v22.8h, v21.8h, v7.h[0]
mls v28.8h, v27.8h, v7.h[0]
sub v20.8h, v19.8h, v22.8h
sub v26.8h, v25.8h, v28.8h
add v19.8h, v19.8h, v22.8h
add v25.8h, v25.8h, v28.8h
sqrdmulh v21.8h, v19.8h, v7.h[1]
sqrdmulh v27.8h, v25.8h, v7.h[1]
sqrdmulh v22.8h, v20.8h, v7.h[1]
sqrdmulh v28.8h, v26.8h, v7.h[1]
sshr v21.8h, v21.8h, #11
sshr v27.8h, v27.8h, #11
sshr v22.8h, v22.8h, #11
sshr v28.8h, v28.8h, #11
mls v19.8h, v21.8h, v7.h[0]
mls v25.8h, v27.8h, v7.h[0]
mls v20.8h, v22.8h, v7.h[0]
mls v26.8h, v28.8h, v7.h[0]
zip1 v21.4s, v19.4s, v20.4s
zip1 v27.4s, v25.4s, v26.4s
zip2 v22.4s, v19.4s, v20.4s
zip2 v28.4s, v25.4s, v26.4s
str q21, [x0, #320]
str q27, [x0, #352]
str q22, [x0, #336]
str q28, [x0, #368]
ldr q31, [x0, #384]
ldr q18, [x0, #416]
ldr q4, [x0, #400]
ldr q19, [x0, #432]
sqrdmulh v5.8h, v4.8h, v3.h[1]
sqrdmulh v20.8h, v19.8h, v3.h[3]
mul v6.8h, v4.8h, v3.h[0]
mul v21.8h, v19.8h, v3.h[2]
mls v6.8h, v5.8h, v7.h[0]
mls v21.8h, v20.8h, v7.h[0]
sub v4.8h, v31.8h, v6.8h
sub v19.8h, v18.8h, v21.8h
add v31.8h, v31.8h, v6.8h
add v18.8h, v18.8h, v21.8h
trn1 v5.2d, v31.2d, v4.2d
trn1 v20.2d, v18.2d, v19.2d
trn2 v6.2d, v31.2d, v4.2d
trn2 v21.2d, v18.2d, v19.2d
ldr q16, [x2, #912]
ldr q22, [x2, #976]
ldr q17, [x2, #928]
ldr q23, [x2, #992]
sqrdmulh v31.8h, v6.8h, v17.8h
sqrdmulh v18.8h, v21.8h, v23.8h
mul v4.8h, v6.8h, v16.8h
mul v19.8h, v21.8h, v22.8h
mls v4.8h, v31.8h, v7.h[0]
mls v19.8h, v18.8h, v7.h[0]
sub v6.8h, v5.8h, v4.8h
sub v21.8h, v20.8h, v19.8h
add v5.8h, v5.8h, v4.8h
add v20.8h, v20.8h, v19.8h
trn1 v31.4s, v5.4s, v6.4s
trn1 v18.4s, v20.4s, v21.4s
trn2 v4.4s, v5.4s, v6.4s
trn2 v19.4s, v20.4s, v21.4s
ldr q16, [x2, #944]
ldr q22, [x2, #1008]
ldr q17, [x2, #960]
ldr q23, [x2, #1024]
sqrdmulh v5.8h, v4.8h, v17.8h
sqrdmulh v20.8h, v19.8h, v23.8h
mul v6.8h, v4.8h, v16.8h
mul v21.8h, v19.8h, v22.8h
mls v6.8h, v5.8h, v7.h[0]
mls v21.8h, v20.8h, v7.h[0]
sub v4.8h, v31.8h, v6.8h
sub v19.8h, v18.8h, v21.8h
add v31.8h, v31.8h, v6.8h
add v18.8h, v18.8h, v21.8h
sqrdmulh v5.8h, v31.8h, v7.h[1]
sqrdmulh v20.8h, v18.8h, v7.h[1]
sqrdmulh v6.8h, v4.8h, v7.h[1]
sqrdmulh v21.8h, v19.8h, v7.h[1]
sshr v5.8h, v5.8h, #11
sshr v20.8h, v20.8h, #11
sshr v6.8h, v6.8h, #11
sshr v21.8h, v21.8h, #11
mls v31.8h, v5.8h, v7.h[0]
mls v18.8h, v20.8h, v7.h[0]
mls v4.8h, v6.8h, v7.h[0]
mls v19.8h, v21.8h, v7.h[0]
zip1 v5.4s, v31.4s, v4.4s
zip1 v20.4s, v18.4s, v19.4s
zip2 v6.4s, v31.4s, v4.4s
zip2 v21.4s, v18.4s, v19.4s
str q5, [x0, #384]
str q20, [x0, #416]
str q6, [x0, #400]
str q21, [x0, #432]
ldr q24, [x0, #448]
ldr q30, [x0, #480]
ldr q25, [x0, #464]
ldr q31, [x0, #496]
sqrdmulh v26.8h, v25.8h, v3.h[5]
sqrdmulh v4.8h, v31.8h, v3.h[7]
mul v27.8h, v25.8h, v3.h[4]
mul v5.8h, v31.8h, v3.h[6]
mls v27.8h, v26.8h, v7.h[0]
mls v5.8h, v4.8h, v7.h[0]
sub v25.8h, v24.8h, v27.8h
sub v31.8h, v30.8h, v5.8h
add v24.8h, v24.8h, v27.8h
add v30.8h, v30.8h, v5.8h
trn1 v26.2d, v24.2d, v25.2d
trn1 v4.2d, v30.2d, v31.2d
trn2 v27.2d, v24.2d, v25.2d
trn2 v5.2d, v30.2d, v31.2d
ldr q28, [x2, #1040]
ldr q6, [x2, #1104]
ldr q29, [x2, #1056]
ldr q16, [x2, #1120]
sqrdmulh v24.8h, v27.8h, v29.8h
sqrdmulh v30.8h, v5.8h, v16.8h
mul v25.8h, v27.8h, v28.8h
mul v31.8h, v5.8h, v6.8h
mls v25.8h, v24.8h, v7.h[0]
mls v31.8h, v30.8h, v7.h[0]
sub v27.8h, v26.8h, v25.8h
sub v5.8h, v4.8h, v31.8h
add v26.8h, v26.8h, v25.8h
add v4.8h, v4.8h, v31.8h
trn1 v24.4s, v26.4s, v27.4s
trn1 v30.4s, v4.4s, v5.4s
trn2 v25.4s, v26.4s, v27.4s
trn2 v31.4s, v4.4s, v5.4s
ldr q28, [x2, #1072]
ldr q6, [x2, #1136]
ldr q29, [x2, #1088]
ldr q16, [x2, #1152]
sqrdmulh v26.8h, v25.8h, v29.8h
sqrdmulh v4.8h, v31.8h, v16.8h
mul v27.8h, v25.8h, v28.8h
mul v5.8h, v31.8h, v6.8h
mls v27.8h, v26.8h, v7.h[0]
mls v5.8h, v4.8h, v7.h[0]
sub v25.8h, v24.8h, v27.8h
sub v31.8h, v30.8h, v5.8h
add v24.8h, v24.8h, v27.8h
add v30.8h, v30.8h, v5.8h
sqrdmulh v26.8h, v24.8h, v7.h[1]
sqrdmulh v4.8h, v30.8h, v7.h[1]
sqrdmulh v27.8h, v25.8h, v7.h[1]
sqrdmulh v5.8h, v31.8h, v7.h[1]
sshr v26.8h, v26.8h, #11
sshr v4.8h, v4.8h, #11
sshr v27.8h, v27.8h, #11
sshr v5.8h, v5.8h, #11
mls v24.8h, v26.8h, v7.h[0]
mls v30.8h, v4.8h, v7.h[0]
mls v25.8h, v27.8h, v7.h[0]
mls v31.8h, v5.8h, v7.h[0]
zip1 v26.4s, v24.4s, v25.4s
zip1 v4.4s, v30.4s, v31.4s
zip2 v27.4s, v24.4s, v25.4s
zip2 v5.4s, v30.4s, v31.4s
str q26, [x0, #448]
str q4, [x0, #480]
str q27, [x0, #464]
str q5, [x0, #496]
ret
.section .rodata
.p2align 4
cr_fwd_z22_t:
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
.hword 3329
.hword 20159
.hword 3329
.hword 20159
.hword 3329
.hword 20159
.hword 3329
.hword 20159
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
.globl cr_inv_z22
.p2align 4
cr_inv_z22:
adrp x2, cr_inv_z22_t
add x2, x2, :lo12:cr_inv_z22_t
ldr q0, [x2, #0]
ldr q1, [x2, #16]
ldr q2, [x2, #32]
ldr q3, [x2, #48]
ldr q7, [x2, #64]
ldr q16, [x0, #0]
ldr q22, [x0, #32]
ldr q17, [x0, #16]
ldr q23, [x0, #48]
uzp1 v18.4s, v16.4s, v17.4s
uzp1 v24.4s, v22.4s, v23.4s
uzp2 v19.4s, v16.4s, v17.4s
uzp2 v25.4s, v22.4s, v23.4s
ldr q20, [x2, #80]
ldr q26, [x2, #144]
ldr q21, [x2, #96]
ldr q27, [x2, #160]
sub v16.8h, v19.8h, v18.8h
sub v22.8h, v25.8h, v24.8h
add v18.8h, v18.8h, v19.8h
add v24.8h, v24.8h, v25.8h
sqrdmulh v17.8h, v16.8h, v21.8h
sqrdmulh v23.8h, v22.8h, v27.8h
mul v16.8h, v16.8h, v20.8h
mul v22.8h, v22.8h, v26.8h
mls v16.8h, v17.8h, v7.h[0]
mls v22.8h, v23.8h, v7.h[0]
trn1 v17.4s, v18.4s, v16.4s
trn1 v23.4s, v24.4s, v22.4s
trn2 v19.4s, v18.4s, v16.4s
trn2 v25.4s, v24.4s, v22.4s
ldr q20, [x2, #112]
ldr q26, [x2, #176]
ldr q21, [x2, #128]
ldr q27, [x2, #192]
sub v16.8h, v19.8h, v17.8h
sub v22.8h, v25.8h, v23.8h
add v17.8h, v17.8h, v19.8h
add v23.8h, v23.8h, v25.8h
sqrdmulh v18.8h, v16.8h, v21.8h
sqrdmulh v24.8h, v22.8h, v27.8h
mul v16.8h, v16.8h, v20.8h
mul v22.8h, v22.8h, v26.8h
mls v16.8h, v18.8h, v7.h[0]
mls v22.8h, v24.8h, v7.h[0]
trn1 v18.2d, v17.2d, v16.2d
trn1 v24.2d, v23.2d, v22.2d
trn2 v19.2d, v17.2d, v16.2d
trn2 v25.2d, v23.2d, v22.2d
sub v16.8h, v19.8h, v18.8h
sub v22.8h, v25.8h, v24.8h
add v18.8h, v18.8h, v19.8h
add v24.8h, v24.8h, v25.8h
sqrdmulh v17.8h, v16.8h, v0.h[1]
sqrdmulh v23.8h, v22.8h, v0.h[3]
mul v16.8h, v16.8h, v0.h[0]
mul v22.8h, v22.8h, v0.h[2]
mls v16.8h, v17.8h, v7.h[0]
mls v22.8h, v23.8h, v7.h[0]
str q18, [x0, #0]
str q24, [x0, #32]
str q16, [x0, #16]
str q22, [x0, #48]
ldr q28, [x0, #64]
ldr q6, [x0, #96]
ldr q29, [x0, #80]
ldr q16, [x0, #112]
uzp1 v30.4s, v28.4s, v29.4s
uzp1 v17.4s, v6.4s, v16.4s
uzp2 v31.4s, v28.4s, v29.4s
uzp2 v18.4s, v6.4s, v16.4s
ldr q4, [x2, #208]
ldr q19, [x2, #272]
ldr q5, [x2, #224]
ldr q20, [x2, #288]
sub v28.8h, v31.8h, v30.8h
sub v6.8h, v18.8h, v17.8h
add v30.8h, v30.8h, v31.8h
add v17.8h, v17.8h, v18.8h
sqrdmulh v29.8h, v28.8h, v5.8h
sqrdmulh v16.8h, v6.8h, v20.8h
mul v28.8h, v28.8h, v4.8h
mul v6.8h, v6.8h, v19.8h
mls v28.8h, v29.8h, v7.h[0]
mls v6.8h, v16.8h, v7.h[0]
trn1 v29.4s, v30.4s, v28.4s
trn1 v16.4s, v17.4s, v6.4s
trn2 v31.4s, v30.4s, v28.4s
trn2 v18.4s, v17.4s, v6.4s
ldr q4, [x2, #240]
ldr q19, [x2, #304]
ldr q5, [x2, #256]
ldr q20, [x2, #320]
sub v28.8h, v31.8h, v29.8h
sub v6.8h, v18.8h, v16.8h
add v29.8h, v29.8h, v31.8h
add v16.8h, v16.8h, v18.8h
sqrdmulh v30.8h, v28.8h, v5.8h
sqrdmulh v17.8h, v6.8h, v20.8h
mul v28.8h, v28.8h, v4.8h
mul v6.8h, v6.8h, v19.8h
mls v28.8h, v30.8h, v7.h[0]
mls v6.8h, v17.8h, v7.h[0]
trn1 v30.2d, v29.2d, v28.2d
trn1 v17.2d, v16.2d, v6.2d
trn2 v31.2d, v29.2d, v28.2d
trn2 v18.2d, v16.2d, v6.2d
sub v28.8h, v31.8h, v30.8h
sub v6.8h, v18.8h, v17.8h
add v30.8h, v30.8h, v31.8h
add v17.8h, v17.8h, v18.8h
sqrdmulh v29.8h, v28.8h, v0.h[5]
sqrdmulh v16.8h, v6.8h, v0.h[7]
mul v28.8h, v28.8h, v0.h[4]
mul v6.8h, v6.8h, v0.h[6]
mls v28.8h, v29.8h, v7.h[0]
mls v6.8h, v16.8h, v7.h[0]
str q30, [x0, #64]
str q17, [x0, #96]
str q28, [x0, #80]
str q6, [x0, #112]
ldr q21, [x0, #128]
ldr q27, [x0, #160]
ldr q22, [x0, #144]
ldr q28, [x0, #176]
uzp1 v23.4s, v21.4s, v22.4s
uzp1 v29.4s, v27.4s, v28.4s
uzp2 v24.4s, v21.4s, v22.4s
uzp2 v30.4s, v27.4s, v28.4s
ldr q25, [x2, #336]
ldr q31, [x2, #400]
ldr q26, [x2, #352]
ldr q4, [x2, #416]
sub v21.8h, v24.8h, v23.8h
sub v27.8h, v30.8h, v29.8h
add v23.8h, v23.8h, v24.8h
add v29.8h, v29.8h, v30.8h
sqrdmulh v22.8h, v21.8h, v26.8h
sqrdmulh v28.8h, v27.8h, v4.8h
mul v21.8h, v21.8h, v25.8h
mul v27.8h, v27.8h, v31.8h
mls v21.8h, v22.8h, v7.h[0]
mls v27.8h, v28.8h, v7.h[0]
trn1 v22.4s, v23.4s, v21.4s
trn1 v28.4s, v29.4s, v27.4s
trn2 v24.4s, v23.4s, v21.4s
trn2 v30.4s, v29.4s, v27.4s
ldr q25, [x2, #368]
ldr q31, [x2, #432]
ldr q26, [x2, #384]
ldr q4, [x2, #448]
sub v21.8h, v24.8h, v22.8h
sub v27.8h, v30.8h, v28.8h
add v22.8h, v22.8h, v24.8h
add v28.8h, v28.8h, v30.8h
sqrdmulh v23.8h, v21.8h, v26.8h
sqrdmulh v29.8h, v27.8h, v4.8h
mul v21.8h, v21.8h, v25.8h
mul v27.8h, v27.8h, v31.8h
mls v21.8h, v23.8h, v7.h[0]
mls v27.8h, v29.8h, v7.h[0]
trn1 v23.2d, v22.2d, v21.2d
trn1 v29.2d, v28.2d, v27.2d
trn2 v24.2d, v22.2d, v21.2d
trn2 v30.2d, v28.2d, v27.2d
sub v21.8h, v24.8h, v23.8h
sub v27.8h, v30.8h, v29.8h
add v23.8h, v23.8h, v24.8h
add v29.8h, v29.8h, v30.8h
sqrdmulh v22.8h, v21.8h, v1.h[1]
sqrdmulh v28.8h, v27.8h, v1.h[3]
mul v21.8h, v21.8h, v1.h[0]
mul v27.8h, v27.8h, v1.h[2]
mls v21.8h, v22.8h, v7.h[0]
mls v27.8h, v28.8h, v7.h[0]
str q23, [x0, #128]
str q29, [x0, #160]
str q21, [x0, #144]
str q27, [x0, #176]
ldr q5, [x0, #192]
ldr q20, [x0, #224]
ldr q6, [x0, #208]
ldr q21, [x0, #240]
uzp1 v16.4s, v5.4s, v6.4s
uzp1 v22.4s, v20.4s, v21.4s
uzp2 v17.4s, v5.4s, v6.4s
uzp2 v23.4s, v20.4s, v21.4s
ldr q18, [x2, #464]
ldr q24, [x2, #528]
ldr q19, [x2, #480]
ldr q25, [x2, #544]
sub v5.8h, v17.8h, v16.8h
sub v20.8h, v23.8h, v22.8h
add v16.8h, v16.8h, v17.8h
add v22.8h, v22.8h, v23.8h
sqrdmulh v6.8h, v5.8h, v19.8h
sqrdmulh v21.8h, v20.8h, v25.8h
mul v5.8h, v5.8h, v18.8h
mul v20.8h, v20.8h, v24.8h
mls v5.8h, v6.8h, v7.h[0]
mls v20.8h, v21.8h, v7.h[0]
trn1 v6.4s, v16.4s, v5.4s
trn1 v21.4s, v22.4s, v20.4s
trn2 v17.4s, v16.4s, v5.4s
trn2 v23.4s, v22.4s, v20.4s
ldr q18, [x2, #496]
ldr q24, [x2, #560]
ldr q19, [x2, #512]
ldr q25, [x2, #576]
sub v5.8h, v17.8h, v6.8h
sub v20.8h, v23.8h, v21.8h
add v6.8h, v6.8h, v17.8h
add v21.8h, v21.8h, v23.8h
sqrdmulh v16.8h, v5.8h, v19.8h
sqrdmulh v22.8h, v20.8h, v25.8h
mul v5.8h, v5.8h, v18.8h
mul v20.8h, v20.8h, v24.8h
mls v5.8h, v16.8h, v7.h[0]
mls v20.8h, v22.8h, v7.h[0]
trn1 v16.2d, v6.2d, v5.2d
trn1 v22.2d, v21.2d, v20.2d
trn2 v17.2d, v6.2d, v5.2d
trn2 v23.2d, v21.2d, v20.2d
sub v5.8h, v17.8h, v16.8h
sub v20.8h, v23.8h, v22.8h
add v16.8h, v16.8h, v17.8h
add v22.8h, v22.8h, v23.8h
sqrdmulh v6.8h, v5.8h, v1.h[5]
sqrdmulh v21.8h, v20.8h, v1.h[7]
mul v5.8h, v5.8h, v1.h[4]
mul v20.8h, v20.8h, v1.h[6]
mls v5.8h, v6.8h, v7.h[0]
mls v20.8h, v21.8h, v7.h[0]
str q16, [x0, #192]
str q22, [x0, #224]
str q5, [x0, #208]
str q20, [x0, #240]
ldr q26, [x0, #256]
ldr q4, [x0, #288]
ldr q27, [x0, #272]
ldr q5, [x0, #304]
uzp1 v28.4s, v26.4s, v27.4s
uzp1 v6.4s, v4.4s, v5.4s
uzp2 v29.4s, v26.4s, v27.4s
uzp2 v16.4s, v4.4s, v5.4s
ldr q30, [x2, #592]
ldr q17, [x2, #656]
ldr q31, [x2, #608]
ldr q18, [x2, #672]
sub v26.8h, v29.8h, v28.8h
sub v4.8h, v16.8h, v6.8h
add v28.8h, v28.8h, v29.8h
add v6.8h, v6.8h, v16.8h
sqrdmulh v27.8h, v26.8h, v31.8h
sqrdmulh v5.8h, v4.8h, v18.8h
mul v26.8h, v26.8h, v30.8h
mul v4.8h, v4.8h, v17.8h
mls v26.8h, v27.8h, v7.h[0]
mls v4.8h, v5.8h, v7.h[0]
trn1 v27.4s, v28.4s, v26.4s
trn1 v5.4s, v6.4s, v4.4s
trn2 v29.4s, v28.4s, v26.4s
trn2 v16.4s, v6.4s, v4.4s
ldr q30, [x2, #624]
ldr q17, [x2, #688]
ldr q31, [x2, #640]
ldr q18, [x2, #704]
sub v26.8h, v29.8h, v27.8h
sub v4.8h, v16.8h, v5.8h
add v27.8h, v27.8h, v29.8h
add v5.8h, v5.8h, v16.8h
sqrdmulh v28.8h, v26.8h, v31.8h
sqrdmulh v6.8h, v4.8h, v18.8h
mul v26.8h, v26.8h, v30.8h
mul v4.8h, v4.8h, v17.8h
mls v26.8h, v28.8h, v7.h[0]
mls v4.8h, v6.8h, v7.h[0]
trn1 v28.2d, v27.2d, v26.2d
trn1 v6.2d, v5.2d, v4.2d
trn2 v29.2d, v27.2d, v26.2d
trn2 v16.2d, v5.2d, v4.2d
sub v26.8h, v29.8h, v28.8h
sub v4.8h, v16.8h, v6.8h
add v28.8h, v28.8h, v29.8h
add v6.8h, v6.8h, v16.8h
sqrdmulh v27.8h, v26.8h, v2.h[1]
sqrdmulh v5.8h, v4.8h, v2.h[3]
mul v26.8h, v26.8h, v2.h[0]
mul v4.8h, v4.8h, v2.h[2]
mls v26.8h, v27.8h, v7.h[0]
mls v4.8h, v5.8h, v7.h[0]
str q28, [x0, #256]
str q6, [x0, #288]
str q26, [x0, #272]
str q4, [x0, #304]
ldr q19, [x0, #320]
ldr q25, [x0, #352]
ldr q20, [x0, #336]
ldr q26, [x0, #368]
uzp1 v21.4s, v19.4s, v20.4s
uzp1 v27.4s, v25.4s, v26.4s
uzp2 v22.4s, v19.4s, v20.4s
uzp2 v28.4s, v25.4s, v26.4s
ldr q23, [x2, #720]
ldr q29, [x2, #784]
ldr q24, [x2, #736]
ldr q30, [x2, #800]
sub v19.8h, v22.8h, v21.8h
sub v25.8h, v28.8h, v27.8h
add v21.8h, v21.8h, v22.8h
add v27.8h, v27.8h, v28.8h
sqrdmulh v20.8h, v19.8h, v24.8h
sqrdmulh v26.8h, v25.8h, v30.8h
mul v19.8h, v19.8h, v23.8h
mul v25.8h, v25.8h, v29.8h
mls v19.8h, v20.8h, v7.h[0]
mls v25.8h, v26.8h, v7.h[0]
trn1 v20.4s, v21.4s, v19.4s
trn1 v26.4s, v27.4s, v25.4s
trn2 v22.4s, v21.4s, v19.4s
trn2 v28.4s, v27.4s, v25.4s
ldr q23, [x2, #752]
ldr q29, [x2, #816]
ldr q24, [x2, #768]
ldr q30, [x2, #832]
sub v19.8h, v22.8h, v20.8h
sub v25.8h, v28.8h, v26.8h
add v20.8h, v20.8h, v22.8h
add v26.8h, v26.8h, v28.8h
sqrdmulh v21.8h, v19.8h, v24.8h
sqrdmulh v27.8h, v25.8h, v30.8h
mul v19.8h, v19.8h, v23.8h
mul v25.8h, v25.8h, v29.8h
mls v19.8h, v21.8h, v7.h[0]
mls v25.8h, v27.8h, v7.h[0]
trn1 v21.2d, v20.2d, v19.2d
trn1 v27.2d, v26.2d, v25.2d
trn2 v22.2d, v20.2d, v19.2d
trn2 v28.2d, v26.2d, v25.2d
sub v19.8h, v22.8h, v21.8h
sub v25.8h, v28.8h, v27.8h
add v21.8h, v21.8h, v22.8h
add v27.8h, v27.8h, v28.8h
sqrdmulh v20.8h, v19.8h, v2.h[5]
sqrdmulh v26.8h, v25.8h, v2.h[7]
mul v19.8h, v19.8h, v2.h[4]
mul v25.8h, v25.8h, v2.h[6]
mls v19.8h, v20.8h, v7.h[0]
mls v25.8h, v26.8h, v7.h[0]
str q21, [x0, #320]
str q27, [x0, #352]
str q19, [x0, #336]
str q25, [x0, #368]
ldr q31, [x0, #384]
ldr q18, [x0, #416]
ldr q4, [x0, #400]
ldr q19, [x0, #432]
uzp1 v5.4s, v31.4s, v4.4s
uzp1 v20.4s, v18.4s, v19.4s
uzp2 v6.4s, v31.4s, v4.4s
uzp2 v21.4s, v18.4s, v19.4s
ldr q16, [x2, #848]
ldr q22, [x2, #912]
ldr q17, [x2, #864]
ldr q23, [x2, #928]
sub v31.8h, v6.8h, v5.8h
sub v18.8h, v21.8h, v20.8h
add v5.8h, v5.8h, v6.8h
add v20.8h, v20.8h, v21.8h
sqrdmulh v4.8h, v31.8h, v17.8h
sqrdmulh v19.8h, v18.8h, v23.8h
mul v31.8h, v31.8h, v16.8h
mul v18.8h, v18.8h, v22.8h
mls v31.8h, v4.8h, v7.h[0]
mls v18.8h, v19.8h, v7.h[0]
trn1 v4.4s, v5.4s, v31.4s
trn1 v19.4s, v20.4s, v18.4s
trn2 v6.4s, v5.4s, v31.4s
trn2 v21.4s, v20.4s, v18.4s
ldr q16, [x2, #880]
ldr q22, [x2, #944]
ldr q17, [x2, #896]
ldr q23, [x2, #960]
sub v31.8h, v6.8h, v4.8h
sub v18.8h, v21.8h, v19.8h
add v4.8h, v4.8h, v6.8h
add v19.8h, v19.8h, v21.8h
sqrdmulh v5.8h, v31.8h, v17.8h
sqrdmulh v20.8h, v18.8h, v23.8h
mul v31.8h, v31.8h, v16.8h
mul v18.8h, v18.8h, v22.8h
mls v31.8h, v5.8h, v7.h[0]
mls v18.8h, v20.8h, v7.h[0]
trn1 v5.2d, v4.2d, v31.2d
trn1 v20.2d, v19.2d, v18.2d
trn2 v6.2d, v4.2d, v31.2d
trn2 v21.2d, v19.2d, v18.2d
sub v31.8h, v6.8h, v5.8h
sub v18.8h, v21.8h, v20.8h
add v5.8h, v5.8h, v6.8h
add v20.8h, v20.8h, v21.8h
sqrdmulh v4.8h, v31.8h, v3.h[1]
sqrdmulh v19.8h, v18.8h, v3.h[3]
mul v31.8h, v31.8h, v3.h[0]
mul v18.8h, v18.8h, v3.h[2]
mls v31.8h, v4.8h, v7.h[0]
mls v18.8h, v19.8h, v7.h[0]
str q5, [x0, #384]
str q20, [x0, #416]
str q31, [x0, #400]
str q18, [x0, #432]
ldr q24, [x0, #448]
ldr q30, [x0, #480]
ldr q25, [x0, #464]
ldr q31, [x0, #496]
uzp1 v26.4s, v24.4s, v25.4s
uzp1 v4.4s, v30.4s, v31.4s
uzp2 v27.4s, v24.4s, v25.4s
uzp2 v5.4s, v30.4s, v31.4s
ldr q28, [x2, #976]
ldr q6, [x2, #1040]
ldr q29, [x2, #992]
ldr q16, [x2, #1056]
sub v24.8h, v27.8h, v26.8h
sub v30.8h, v5.8h, v4.8h
add v26.8h, v26.8h, v27.8h
add v4.8h, v4.8h, v5.8h
sqrdmulh v25.8h, v24.8h, v29.8h
sqrdmulh v31.8h, v30.8h, v16.8h
mul v24.8h, v24.8h, v28.8h
mul v30.8h, v30.8h, v6.8h
mls v24.8h, v25.8h, v7.h[0]
mls v30.8h, v31.8h, v7.h[0]
trn1 v25.4s, v26.4s, v24.4s
trn1 v31.4s, v4.4s, v30.4s
trn2 v27.4s, v26.4s, v24.4s
trn2 v5.4s, v4.4s, v30.4s
ldr q28, [x2, #1008]
ldr q6, [x2, #1072]
ldr q29, [x2, #1024]
ldr q16, [x2, #1088]
sub v24.8h, v27.8h, v25.8h
sub v30.8h, v5.8h, v31.8h
add v25.8h, v25.8h, v27.8h
add v31.8h, v31.8h, v5.8h
sqrdmulh v26.8h, v24.8h, v29.8h
sqrdmulh v4.8h, v30.8h, v16.8h
mul v24.8h, v24.8h, v28.8h
mul v30.8h, v30.8h, v6.8h
mls v24.8h, v26.8h, v7.h[0]
mls v30.8h, v4.8h, v7.h[0]
trn1 v26.2d, v25.2d, v24.2d
trn1 v4.2d, v31.2d, v30.2d
trn2 v27.2d, v25.2d, v24.2d
trn2 v5.2d, v31.2d, v30.2d
sub v24.8h, v27.8h, v26.8h
sub v30.8h, v5.8h, v4.8h
add v26.8h, v26.8h, v27.8h
add v4.8h, v4.8h, v5.8h
sqrdmulh v25.8h, v24.8h, v3.h[5]
sqrdmulh v31.8h, v30.8h, v3.h[7]
mul v24.8h, v24.8h, v3.h[4]
mul v30.8h, v30.8h, v3.h[6]
mls v24.8h, v25.8h, v7.h[0]
mls v30.8h, v31.8h, v7.h[0]
str q26, [x0, #448]
str q4, [x0, #480]
str q24, [x0, #464]
str q30, [x0, #496]
ldr q0, [x2, #1104]
ldr q1, [x2, #1120]
ldr q2, [x2, #1136]
ldr q3, [x2, #1152]
ldr q4, [x2, #1168]
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
ldr q7, [x2, #1184]
sub v5.8h, v17.8h, v16.8h
add v16.8h, v16.8h, v17.8h
sub v16.8h, v16.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v2.h[3]
mul v17.8h, v5.8h, v2.h[2]
mls v17.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v16.8h, v0.h[3]
mul v16.8h, v16.8h, v0.h[2]
mls v16.8h, v6.8h, v0.h[0]
sub v5.8h, v19.8h, v18.8h
add v18.8h, v18.8h, v19.8h
sub v18.8h, v18.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v2.h[1]
mul v19.8h, v5.8h, v2.h[0]
mls v19.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v18.8h, v0.h[3]
mul v18.8h, v18.8h, v0.h[2]
mls v18.8h, v6.8h, v0.h[0]
sub v5.8h, v21.8h, v20.8h
add v20.8h, v20.8h, v21.8h
sub v20.8h, v20.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v1.h[7]
mul v21.8h, v5.8h, v1.h[6]
mls v21.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v20.8h, v0.h[3]
mul v20.8h, v20.8h, v0.h[2]
mls v20.8h, v6.8h, v0.h[0]
sub v5.8h, v23.8h, v22.8h
add v22.8h, v22.8h, v23.8h
sub v22.8h, v22.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v1.h[5]
mul v23.8h, v5.8h, v1.h[4]
mls v23.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v22.8h, v0.h[3]
mul v22.8h, v22.8h, v0.h[2]
mls v22.8h, v6.8h, v0.h[0]
sub v5.8h, v25.8h, v24.8h
add v24.8h, v24.8h, v25.8h
sub v24.8h, v24.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v1.h[3]
mul v25.8h, v5.8h, v1.h[2]
mls v25.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v24.8h, v0.h[3]
mul v24.8h, v24.8h, v0.h[2]
mls v24.8h, v6.8h, v0.h[0]
sub v5.8h, v27.8h, v26.8h
add v26.8h, v26.8h, v27.8h
sub v26.8h, v26.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v1.h[1]
mul v27.8h, v5.8h, v1.h[0]
mls v27.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v26.8h, v0.h[3]
mul v26.8h, v26.8h, v0.h[2]
mls v26.8h, v6.8h, v0.h[0]
sub v5.8h, v29.8h, v28.8h
add v28.8h, v28.8h, v29.8h
sub v28.8h, v28.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v0.h[7]
mul v29.8h, v5.8h, v0.h[6]
mls v29.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v28.8h, v0.h[3]
mul v28.8h, v28.8h, v0.h[2]
mls v28.8h, v6.8h, v0.h[0]
sub v5.8h, v31.8h, v30.8h
add v30.8h, v30.8h, v31.8h
sub v30.8h, v30.8h, v7.8h
sqrdmulh v6.8h, v5.8h, v0.h[5]
mul v31.8h, v5.8h, v0.h[4]
mls v31.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v30.8h, v0.h[3]
mul v30.8h, v30.8h, v0.h[2]
mls v30.8h, v6.8h, v0.h[0]
sub v5.8h, v18.8h, v16.8h
add v16.8h, v16.8h, v18.8h
sqrdmulh v6.8h, v5.8h, v4.h[1]
mul v18.8h, v5.8h, v4.h[0]
mls v18.8h, v6.8h, v0.h[0]
sub v5.8h, v19.8h, v17.8h
add v17.8h, v17.8h, v19.8h
sqrdmulh v6.8h, v5.8h, v4.h[1]
mul v19.8h, v5.8h, v4.h[0]
mls v19.8h, v6.8h, v0.h[0]
sub v5.8h, v22.8h, v20.8h
add v20.8h, v20.8h, v22.8h
sqrdmulh v6.8h, v5.8h, v3.h[7]
mul v22.8h, v5.8h, v3.h[6]
mls v22.8h, v6.8h, v0.h[0]
sub v5.8h, v23.8h, v21.8h
add v21.8h, v21.8h, v23.8h
sqrdmulh v6.8h, v5.8h, v3.h[7]
mul v23.8h, v5.8h, v3.h[6]
mls v23.8h, v6.8h, v0.h[0]
sub v5.8h, v26.8h, v24.8h
add v24.8h, v24.8h, v26.8h
sqrdmulh v6.8h, v5.8h, v3.h[5]
mul v26.8h, v5.8h, v3.h[4]
mls v26.8h, v6.8h, v0.h[0]
sub v5.8h, v27.8h, v25.8h
add v25.8h, v25.8h, v27.8h
sqrdmulh v6.8h, v5.8h, v3.h[5]
mul v27.8h, v5.8h, v3.h[4]
mls v27.8h, v6.8h, v0.h[0]
sub v5.8h, v30.8h, v28.8h
add v28.8h, v28.8h, v30.8h
sqrdmulh v6.8h, v5.8h, v3.h[3]
mul v30.8h, v5.8h, v3.h[2]
mls v30.8h, v6.8h, v0.h[0]
sub v5.8h, v31.8h, v29.8h
add v29.8h, v29.8h, v31.8h
sqrdmulh v6.8h, v5.8h, v3.h[3]
mul v31.8h, v5.8h, v3.h[2]
mls v31.8h, v6.8h, v0.h[0]
sub v5.8h, v20.8h, v16.8h
add v16.8h, v16.8h, v20.8h
sqrdmulh v6.8h, v5.8h, v3.h[1]
mul v20.8h, v5.8h, v3.h[0]
mls v20.8h, v6.8h, v0.h[0]
sub v5.8h, v21.8h, v17.8h
add v17.8h, v17.8h, v21.8h
sqrdmulh v6.8h, v5.8h, v3.h[1]
mul v21.8h, v5.8h, v3.h[0]
mls v21.8h, v6.8h, v0.h[0]
sub v5.8h, v22.8h, v18.8h
add v18.8h, v18.8h, v22.8h
sqrdmulh v6.8h, v5.8h, v3.h[1]
mul v22.8h, v5.8h, v3.h[0]
mls v22.8h, v6.8h, v0.h[0]
sub v5.8h, v23.8h, v19.8h
add v19.8h, v19.8h, v23.8h
sqrdmulh v6.8h, v5.8h, v3.h[1]
mul v23.8h, v5.8h, v3.h[0]
mls v23.8h, v6.8h, v0.h[0]
sub v5.8h, v28.8h, v24.8h
add v24.8h, v24.8h, v28.8h
sqrdmulh v6.8h, v5.8h, v2.h[7]
mul v28.8h, v5.8h, v2.h[6]
mls v28.8h, v6.8h, v0.h[0]
sub v5.8h, v29.8h, v25.8h
add v25.8h, v25.8h, v29.8h
sqrdmulh v6.8h, v5.8h, v2.h[7]
mul v29.8h, v5.8h, v2.h[6]
mls v29.8h, v6.8h, v0.h[0]
sub v5.8h, v30.8h, v26.8h
add v26.8h, v26.8h, v30.8h
sqrdmulh v6.8h, v5.8h, v2.h[7]
mul v30.8h, v5.8h, v2.h[6]
mls v30.8h, v6.8h, v0.h[0]
sub v5.8h, v31.8h, v27.8h
add v27.8h, v27.8h, v31.8h
sqrdmulh v6.8h, v5.8h, v2.h[7]
mul v31.8h, v5.8h, v2.h[6]
mls v31.8h, v6.8h, v0.h[0]
ldr q7, [x2, #1200]
sub v5.8h, v24.8h, v16.8h
add v16.8h, v16.8h, v24.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v24.8h, v5.8h, v2.h[4]
mls v24.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v16.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v16.8h, v6.8h, v0.h[0]
sshr v6.8h, v24.8h, #15
and v6.16b, v6.16b, v7.16b
add v24.8h, v24.8h, v6.8h
sub v5.8h, v25.8h, v17.8h
add v17.8h, v17.8h, v25.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v25.8h, v5.8h, v2.h[4]
mls v25.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v17.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v17.8h, v6.8h, v0.h[0]
sshr v6.8h, v25.8h, #15
and v6.16b, v6.16b, v7.16b
add v25.8h, v25.8h, v6.8h
sub v5.8h, v26.8h, v18.8h
add v18.8h, v18.8h, v26.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v26.8h, v5.8h, v2.h[4]
mls v26.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v18.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v18.8h, v6.8h, v0.h[0]
sshr v6.8h, v26.8h, #15
and v6.16b, v6.16b, v7.16b
add v26.8h, v26.8h, v6.8h
sub v5.8h, v27.8h, v19.8h
add v19.8h, v19.8h, v27.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v27.8h, v5.8h, v2.h[4]
mls v27.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v19.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v19.8h, v6.8h, v0.h[0]
sshr v6.8h, v27.8h, #15
and v6.16b, v6.16b, v7.16b
add v27.8h, v27.8h, v6.8h
sub v5.8h, v28.8h, v20.8h
add v20.8h, v20.8h, v28.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v28.8h, v5.8h, v2.h[4]
mls v28.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v20.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v20.8h, v6.8h, v0.h[0]
sshr v6.8h, v28.8h, #15
and v6.16b, v6.16b, v7.16b
add v28.8h, v28.8h, v6.8h
sub v5.8h, v29.8h, v21.8h
add v21.8h, v21.8h, v29.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v29.8h, v5.8h, v2.h[4]
mls v29.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v21.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v21.8h, v6.8h, v0.h[0]
sshr v6.8h, v29.8h, #15
and v6.16b, v6.16b, v7.16b
add v29.8h, v29.8h, v6.8h
sub v5.8h, v30.8h, v22.8h
add v22.8h, v22.8h, v30.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v30.8h, v5.8h, v2.h[4]
mls v30.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v22.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v22.8h, v6.8h, v0.h[0]
sshr v6.8h, v30.8h, #15
and v6.16b, v6.16b, v7.16b
add v30.8h, v30.8h, v6.8h
sub v5.8h, v31.8h, v23.8h
add v23.8h, v23.8h, v31.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v31.8h, v5.8h, v2.h[4]
mls v31.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v23.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v23.8h, v6.8h, v0.h[0]
sshr v6.8h, v31.8h, #15
and v6.16b, v6.16b, v7.16b
add v31.8h, v31.8h, v6.8h
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
sub v5.8h, v17.8h, v16.8h
add v16.8h, v16.8h, v17.8h
sqrdmulh v6.8h, v5.8h, v2.h[3]
mul v17.8h, v5.8h, v2.h[2]
mls v17.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v16.8h, v0.h[3]
mul v16.8h, v16.8h, v0.h[2]
mls v16.8h, v6.8h, v0.h[0]
sub v5.8h, v19.8h, v18.8h
add v18.8h, v18.8h, v19.8h
sqrdmulh v6.8h, v5.8h, v2.h[1]
mul v19.8h, v5.8h, v2.h[0]
mls v19.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v18.8h, v0.h[3]
mul v18.8h, v18.8h, v0.h[2]
mls v18.8h, v6.8h, v0.h[0]
sub v5.8h, v21.8h, v20.8h
add v20.8h, v20.8h, v21.8h
sqrdmulh v6.8h, v5.8h, v1.h[7]
mul v21.8h, v5.8h, v1.h[6]
mls v21.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v20.8h, v0.h[3]
mul v20.8h, v20.8h, v0.h[2]
mls v20.8h, v6.8h, v0.h[0]
sub v5.8h, v23.8h, v22.8h
add v22.8h, v22.8h, v23.8h
sqrdmulh v6.8h, v5.8h, v1.h[5]
mul v23.8h, v5.8h, v1.h[4]
mls v23.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v22.8h, v0.h[3]
mul v22.8h, v22.8h, v0.h[2]
mls v22.8h, v6.8h, v0.h[0]
sub v5.8h, v25.8h, v24.8h
add v24.8h, v24.8h, v25.8h
sqrdmulh v6.8h, v5.8h, v1.h[3]
mul v25.8h, v5.8h, v1.h[2]
mls v25.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v24.8h, v0.h[3]
mul v24.8h, v24.8h, v0.h[2]
mls v24.8h, v6.8h, v0.h[0]
sub v5.8h, v27.8h, v26.8h
add v26.8h, v26.8h, v27.8h
sqrdmulh v6.8h, v5.8h, v1.h[1]
mul v27.8h, v5.8h, v1.h[0]
mls v27.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v26.8h, v0.h[3]
mul v26.8h, v26.8h, v0.h[2]
mls v26.8h, v6.8h, v0.h[0]
sub v5.8h, v29.8h, v28.8h
add v28.8h, v28.8h, v29.8h
sqrdmulh v6.8h, v5.8h, v0.h[7]
mul v29.8h, v5.8h, v0.h[6]
mls v29.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v28.8h, v0.h[3]
mul v28.8h, v28.8h, v0.h[2]
mls v28.8h, v6.8h, v0.h[0]
sub v5.8h, v31.8h, v30.8h
add v30.8h, v30.8h, v31.8h
sqrdmulh v6.8h, v5.8h, v0.h[5]
mul v31.8h, v5.8h, v0.h[4]
mls v31.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v30.8h, v0.h[3]
mul v30.8h, v30.8h, v0.h[2]
mls v30.8h, v6.8h, v0.h[0]
sub v5.8h, v18.8h, v16.8h
add v16.8h, v16.8h, v18.8h
sqrdmulh v6.8h, v5.8h, v4.h[1]
mul v18.8h, v5.8h, v4.h[0]
mls v18.8h, v6.8h, v0.h[0]
sub v5.8h, v19.8h, v17.8h
add v17.8h, v17.8h, v19.8h
sqrdmulh v6.8h, v5.8h, v4.h[1]
mul v19.8h, v5.8h, v4.h[0]
mls v19.8h, v6.8h, v0.h[0]
sub v5.8h, v22.8h, v20.8h
add v20.8h, v20.8h, v22.8h
sqrdmulh v6.8h, v5.8h, v3.h[7]
mul v22.8h, v5.8h, v3.h[6]
mls v22.8h, v6.8h, v0.h[0]
sub v5.8h, v23.8h, v21.8h
add v21.8h, v21.8h, v23.8h
sqrdmulh v6.8h, v5.8h, v3.h[7]
mul v23.8h, v5.8h, v3.h[6]
mls v23.8h, v6.8h, v0.h[0]
sub v5.8h, v26.8h, v24.8h
add v24.8h, v24.8h, v26.8h
sqrdmulh v6.8h, v5.8h, v3.h[5]
mul v26.8h, v5.8h, v3.h[4]
mls v26.8h, v6.8h, v0.h[0]
sub v5.8h, v27.8h, v25.8h
add v25.8h, v25.8h, v27.8h
sqrdmulh v6.8h, v5.8h, v3.h[5]
mul v27.8h, v5.8h, v3.h[4]
mls v27.8h, v6.8h, v0.h[0]
sub v5.8h, v30.8h, v28.8h
add v28.8h, v28.8h, v30.8h
sqrdmulh v6.8h, v5.8h, v3.h[3]
mul v30.8h, v5.8h, v3.h[2]
mls v30.8h, v6.8h, v0.h[0]
sub v5.8h, v31.8h, v29.8h
add v29.8h, v29.8h, v31.8h
sqrdmulh v6.8h, v5.8h, v3.h[3]
mul v31.8h, v5.8h, v3.h[2]
mls v31.8h, v6.8h, v0.h[0]
sub v5.8h, v20.8h, v16.8h
add v16.8h, v16.8h, v20.8h
sqrdmulh v6.8h, v5.8h, v3.h[1]
mul v20.8h, v5.8h, v3.h[0]
mls v20.8h, v6.8h, v0.h[0]
sub v5.8h, v21.8h, v17.8h
add v17.8h, v17.8h, v21.8h
sqrdmulh v6.8h, v5.8h, v3.h[1]
mul v21.8h, v5.8h, v3.h[0]
mls v21.8h, v6.8h, v0.h[0]
sub v5.8h, v22.8h, v18.8h
add v18.8h, v18.8h, v22.8h
sqrdmulh v6.8h, v5.8h, v3.h[1]
mul v22.8h, v5.8h, v3.h[0]
mls v22.8h, v6.8h, v0.h[0]
sub v5.8h, v23.8h, v19.8h
add v19.8h, v19.8h, v23.8h
sqrdmulh v6.8h, v5.8h, v3.h[1]
mul v23.8h, v5.8h, v3.h[0]
mls v23.8h, v6.8h, v0.h[0]
sub v5.8h, v28.8h, v24.8h
add v24.8h, v24.8h, v28.8h
sqrdmulh v6.8h, v5.8h, v2.h[7]
mul v28.8h, v5.8h, v2.h[6]
mls v28.8h, v6.8h, v0.h[0]
sub v5.8h, v29.8h, v25.8h
add v25.8h, v25.8h, v29.8h
sqrdmulh v6.8h, v5.8h, v2.h[7]
mul v29.8h, v5.8h, v2.h[6]
mls v29.8h, v6.8h, v0.h[0]
sub v5.8h, v30.8h, v26.8h
add v26.8h, v26.8h, v30.8h
sqrdmulh v6.8h, v5.8h, v2.h[7]
mul v30.8h, v5.8h, v2.h[6]
mls v30.8h, v6.8h, v0.h[0]
sub v5.8h, v31.8h, v27.8h
add v27.8h, v27.8h, v31.8h
sqrdmulh v6.8h, v5.8h, v2.h[7]
mul v31.8h, v5.8h, v2.h[6]
mls v31.8h, v6.8h, v0.h[0]
ldr q7, [x2, #1200]
sub v5.8h, v24.8h, v16.8h
add v16.8h, v16.8h, v24.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v24.8h, v5.8h, v2.h[4]
mls v24.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v16.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v16.8h, v6.8h, v0.h[0]
sshr v6.8h, v24.8h, #15
and v6.16b, v6.16b, v7.16b
add v24.8h, v24.8h, v6.8h
sub v5.8h, v25.8h, v17.8h
add v17.8h, v17.8h, v25.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v25.8h, v5.8h, v2.h[4]
mls v25.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v17.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v17.8h, v6.8h, v0.h[0]
sshr v6.8h, v25.8h, #15
and v6.16b, v6.16b, v7.16b
add v25.8h, v25.8h, v6.8h
sub v5.8h, v26.8h, v18.8h
add v18.8h, v18.8h, v26.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v26.8h, v5.8h, v2.h[4]
mls v26.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v18.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v18.8h, v6.8h, v0.h[0]
sshr v6.8h, v26.8h, #15
and v6.16b, v6.16b, v7.16b
add v26.8h, v26.8h, v6.8h
sub v5.8h, v27.8h, v19.8h
add v19.8h, v19.8h, v27.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v27.8h, v5.8h, v2.h[4]
mls v27.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v19.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v19.8h, v6.8h, v0.h[0]
sshr v6.8h, v27.8h, #15
and v6.16b, v6.16b, v7.16b
add v27.8h, v27.8h, v6.8h
sub v5.8h, v28.8h, v20.8h
add v20.8h, v20.8h, v28.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v28.8h, v5.8h, v2.h[4]
mls v28.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v20.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v20.8h, v6.8h, v0.h[0]
sshr v6.8h, v28.8h, #15
and v6.16b, v6.16b, v7.16b
add v28.8h, v28.8h, v6.8h
sub v5.8h, v29.8h, v21.8h
add v21.8h, v21.8h, v29.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v29.8h, v5.8h, v2.h[4]
mls v29.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v21.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v21.8h, v6.8h, v0.h[0]
sshr v6.8h, v29.8h, #15
and v6.16b, v6.16b, v7.16b
add v29.8h, v29.8h, v6.8h
sub v5.8h, v30.8h, v22.8h
add v22.8h, v22.8h, v30.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v30.8h, v5.8h, v2.h[4]
mls v30.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v22.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v22.8h, v6.8h, v0.h[0]
sshr v6.8h, v30.8h, #15
and v6.16b, v6.16b, v7.16b
add v30.8h, v30.8h, v6.8h
sub v5.8h, v31.8h, v23.8h
add v23.8h, v23.8h, v31.8h
sqrdmulh v6.8h, v5.8h, v2.h[5]
mul v31.8h, v5.8h, v2.h[4]
mls v31.8h, v6.8h, v0.h[0]
sqrdmulh v6.8h, v23.8h, v0.h[1]
sshr v6.8h, v6.8h, #11
mls v23.8h, v6.8h, v0.h[0]
sshr v6.8h, v31.8h, #15
and v6.16b, v6.16b, v7.16b
add v31.8h, v31.8h, v6.8h
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
cr_inv_z22_t:
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
.hword 3329
.hword 20159
.hword 3329
.hword 20159
.hword 3329
.hword 20159
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
.hword 3329
.hword 20159
.hword 65510
.hword 65280
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
.hword 0
.hword 0
.hword 0
.hword 0
.hword 0
.hword 0
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

