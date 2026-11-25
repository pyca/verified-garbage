.text
.globl cr_fwd_ls
.p2align 4
cr_fwd_ls:
adrp x2, cr_fwd_ls_t
add x2, x2, :lo12:cr_fwd_ls_t
ldr q0, [x2, #0]
ldr q16, [x0, #480]
ldr q17, [x0, #224]
ldr q18, [x0, #352]
ldr q19, [x0, #416]
ldr q20, [x0, #448]
ldr q1, [x2, #16]
ldr q21, [x0, #96]
ldr q22, [x0, #160]
ldr q23, [x0, #192]
ldr q24, [x0, #288]
ldr q25, [x0, #320]
ldr q26, [x0, #384]
ldr q2, [x2, #32]
ldr q3, [x2, #48]
ldr q27, [x0, #32]
ldr q28, [x0, #64]
ldr q29, [x0, #128]
sqrdmulh v30.8h, v16.8h, v0.h[3]
ldr q31, [x0, #256]
mul v16.8h, v16.8h, v0.h[2]
sqrdmulh v4.8h, v18.8h, v0.h[3]
mul v18.8h, v18.8h, v0.h[2]
sqrdmulh v5.8h, v19.8h, v0.h[3]
mls v16.8h, v30.8h, v0.h[0]
mul v30.8h, v19.8h, v0.h[2]
sqrdmulh v19.8h, v20.8h, v0.h[3]
mul v20.8h, v20.8h, v0.h[2]
sub v6.8h, v17.8h, v16.8h
add v16.8h, v17.8h, v16.8h
mls v18.8h, v4.8h, v0.h[0]
sqrdmulh v17.8h, v16.8h, v0.h[5]
mul v16.8h, v16.8h, v0.h[4]
sqrdmulh v7.8h, v6.8h, v0.h[7]
mul v4.8h, v6.8h, v0.h[6]
sub v6.8h, v21.8h, v18.8h
mls v30.8h, v5.8h, v0.h[0]
add v18.8h, v21.8h, v18.8h
mls v20.8h, v19.8h, v0.h[0]
mls v16.8h, v17.8h, v0.h[0]
mls v4.8h, v7.8h, v0.h[0]
ldr q21, [x0, #0]
sqrdmulh v19.8h, v24.8h, v0.h[3]
sub v17.8h, v22.8h, v30.8h
mul v24.8h, v24.8h, v0.h[2]
add v22.8h, v22.8h, v30.8h
sqrdmulh v30.8h, v25.8h, v0.h[3]
sub v5.8h, v23.8h, v20.8h
mul v25.8h, v25.8h, v0.h[2]
add v23.8h, v23.8h, v20.8h
sqrdmulh v20.8h, v26.8h, v0.h[3]
sub v7.8h, v18.8h, v16.8h
mul v26.8h, v26.8h, v0.h[2]
add v16.8h, v18.8h, v16.8h
sqrdmulh v18.8h, v22.8h, v0.h[5]
mul v22.8h, v22.8h, v0.h[4]
mls v24.8h, v19.8h, v0.h[0]
sqrdmulh v19.8h, v23.8h, v0.h[5]
mul v23.8h, v23.8h, v0.h[4]
mls v25.8h, v30.8h, v0.h[0]
sqrdmulh v30.8h, v17.8h, v0.h[7]
mul v17.8h, v17.8h, v0.h[6]
mls v26.8h, v20.8h, v0.h[0]
sub v20.8h, v27.8h, v24.8h
mls v22.8h, v18.8h, v0.h[0]
add v18.8h, v27.8h, v24.8h
sqrdmulh v24.8h, v5.8h, v0.h[7]
sub v27.8h, v6.8h, v4.8h
mul v5.8h, v5.8h, v0.h[6]
add v4.8h, v6.8h, v4.8h
sqrdmulh v6.8h, v16.8h, v1.h[1]
mul v16.8h, v16.8h, v1.h[0]
mls v23.8h, v19.8h, v0.h[0]
sub v19.8h, v28.8h, v25.8h
mls v17.8h, v30.8h, v0.h[0]
add v30.8h, v28.8h, v25.8h
sqrdmulh v25.8h, v7.8h, v1.h[3]
sub v28.8h, v29.8h, v26.8h
mul v7.8h, v7.8h, v1.h[2]
add v29.8h, v29.8h, v26.8h
mls v5.8h, v24.8h, v0.h[0]
sub v26.8h, v18.8h, v22.8h
sqrdmulh v24.8h, v31.8h, v0.h[3]
add v22.8h, v18.8h, v22.8h
mul v18.8h, v31.8h, v0.h[2]
sub v31.8h, v30.8h, v23.8h
mls v16.8h, v6.8h, v0.h[0]
add v23.8h, v30.8h, v23.8h
mls v7.8h, v25.8h, v0.h[0]
sub v30.8h, v20.8h, v17.8h
sqrdmulh v25.8h, v29.8h, v0.h[5]
add v20.8h, v20.8h, v17.8h
mul v17.8h, v29.8h, v0.h[4]
sub v29.8h, v19.8h, v5.8h
sqrdmulh v6.8h, v28.8h, v0.h[7]
add v19.8h, v19.8h, v5.8h
mul v28.8h, v28.8h, v0.h[6]
sub v5.8h, v22.8h, v16.8h
mls v18.8h, v24.8h, v0.h[0]
add v24.8h, v22.8h, v16.8h
sqrdmulh v16.8h, v23.8h, v1.h[1]
sub v22.8h, v26.8h, v7.8h
mul v23.8h, v23.8h, v1.h[0]
add v26.8h, v26.8h, v7.8h
sqrdmulh v7.8h, v31.8h, v1.h[3]
mul v31.8h, v31.8h, v1.h[2]
mls v17.8h, v25.8h, v0.h[0]
sub v25.8h, v21.8h, v18.8h
mls v28.8h, v6.8h, v0.h[0]
add v21.8h, v21.8h, v18.8h
sqrdmulh v18.8h, v4.8h, v1.h[5]
mul v6.8h, v4.8h, v1.h[4]
sqrdmulh v4.8h, v27.8h, v1.h[7]
mul v27.8h, v27.8h, v1.h[6]
mls v23.8h, v16.8h, v0.h[0]
sub v16.8h, v21.8h, v17.8h
mls v6.8h, v18.8h, v0.h[0]
add v18.8h, v21.8h, v17.8h
sqrdmulh v21.8h, v19.8h, v1.h[5]
sub v17.8h, v25.8h, v28.8h
mls v27.8h, v4.8h, v0.h[0]
add v28.8h, v25.8h, v28.8h
mul v25.8h, v19.8h, v1.h[4]
sub v19.8h, v18.8h, v23.8h
sub v4.8h, v20.8h, v6.8h
add v20.8h, v20.8h, v6.8h
sqrdmulh v6.8h, v29.8h, v1.h[7]
add v18.8h, v18.8h, v23.8h
mul v23.8h, v29.8h, v1.h[6]
sub v29.8h, v30.8h, v27.8h
add v30.8h, v30.8h, v27.8h
sqrdmulh v27.8h, v24.8h, v2.h[1]
mul v24.8h, v24.8h, v2.h[0]
mls v31.8h, v7.8h, v0.h[0]
sqrdmulh v7.8h, v5.8h, v2.h[3]
mul v5.8h, v5.8h, v2.h[2]
mls v25.8h, v21.8h, v0.h[0]
sqrdmulh v21.8h, v26.8h, v2.h[5]
mul v26.8h, v26.8h, v2.h[4]
mls v23.8h, v6.8h, v0.h[0]
sub v6.8h, v16.8h, v31.8h
mls v24.8h, v27.8h, v0.h[0]
add v27.8h, v16.8h, v31.8h
sqrdmulh v31.8h, v22.8h, v2.h[7]
sub v16.8h, v28.8h, v25.8h
mul v22.8h, v22.8h, v2.h[6]
add v25.8h, v28.8h, v25.8h
sqrdmulh v28.8h, v20.8h, v3.h[1]
mul v20.8h, v20.8h, v3.h[0]
mls v5.8h, v7.8h, v0.h[0]
sub v7.8h, v17.8h, v23.8h
mls v26.8h, v21.8h, v0.h[0]
add v21.8h, v17.8h, v23.8h
sqrdmulh v17.8h, v4.8h, v3.h[3]
sub v23.8h, v18.8h, v24.8h
mul v4.8h, v4.8h, v3.h[2]
add v18.8h, v18.8h, v24.8h
sqrdmulh v24.8h, v30.8h, v3.h[5]
str q23, [x0, #32]
mul v23.8h, v30.8h, v3.h[4]
sub v30.8h, v19.8h, v5.8h
str q18, [x0, #0]
sqrdmulh v18.8h, v29.8h, v3.h[7]
add v19.8h, v19.8h, v5.8h
mul v29.8h, v29.8h, v3.h[6]
sub v5.8h, v27.8h, v26.8h
str q30, [x0, #96]
mls v22.8h, v31.8h, v0.h[0]
add v30.8h, v27.8h, v26.8h
str q19, [x0, #64]
mls v20.8h, v28.8h, v0.h[0]
str q5, [x0, #160]
ldr q31, [x0, #496]
ldr q26, [x0, #240]
mls v4.8h, v17.8h, v0.h[0]
str q30, [x0, #128]
ldr q27, [x0, #368]
ldr q19, [x0, #432]
mls v23.8h, v24.8h, v0.h[0]
ldr q28, [x0, #464]
mls v29.8h, v18.8h, v0.h[0]
sub v17.8h, v6.8h, v22.8h
add v30.8h, v6.8h, v22.8h
sub v24.8h, v25.8h, v20.8h
add v18.8h, v25.8h, v20.8h
sub v22.8h, v16.8h, v4.8h
str q17, [x0, #224]
ldr q20, [x0, #112]
add v25.8h, v16.8h, v4.8h
sub v17.8h, v21.8h, v23.8h
str q30, [x0, #192]
str q24, [x0, #288]
sqrdmulh v16.8h, v31.8h, v0.h[3]
ldr q30, [x0, #176]
add v24.8h, v21.8h, v23.8h
str q18, [x0, #256]
str q22, [x0, #352]
mul v23.8h, v31.8h, v0.h[2]
ldr q21, [x0, #208]
ldr q18, [x0, #304]
ldr q22, [x0, #336]
sub v31.8h, v7.8h, v29.8h
str q25, [x0, #320]
str q17, [x0, #416]
sqrdmulh v25.8h, v27.8h, v0.h[3]
add v17.8h, v7.8h, v29.8h
str q24, [x0, #384]
mul v29.8h, v27.8h, v0.h[2]
ldr q24, [x0, #400]
ldr q27, [x0, #48]
str q31, [x0, #480]
sqrdmulh v31.8h, v19.8h, v0.h[3]
str q17, [x0, #448]
mls v23.8h, v16.8h, v0.h[0]
ldr q17, [x0, #80]
ldr q16, [x0, #144]
mul v19.8h, v19.8h, v0.h[2]
sqrdmulh v5.8h, v28.8h, v0.h[3]
mul v28.8h, v28.8h, v0.h[2]
sub v6.8h, v26.8h, v23.8h
add v23.8h, v26.8h, v23.8h
mls v29.8h, v25.8h, v0.h[0]
sqrdmulh v26.8h, v23.8h, v0.h[5]
mul v25.8h, v23.8h, v0.h[4]
sqrdmulh v23.8h, v6.8h, v0.h[7]
mul v4.8h, v6.8h, v0.h[6]
sub v7.8h, v20.8h, v29.8h
mls v19.8h, v31.8h, v0.h[0]
add v31.8h, v20.8h, v29.8h
mls v28.8h, v5.8h, v0.h[0]
mls v25.8h, v26.8h, v0.h[0]
ldr q29, [x0, #272]
mls v4.8h, v23.8h, v0.h[0]
ldr q20, [x0, #16]
sqrdmulh v26.8h, v18.8h, v0.h[3]
add v23.8h, v30.8h, v19.8h
mul v18.8h, v18.8h, v0.h[2]
sub v30.8h, v30.8h, v19.8h
sqrdmulh v19.8h, v22.8h, v0.h[3]
sub v6.8h, v21.8h, v28.8h
mul v22.8h, v22.8h, v0.h[2]
add v21.8h, v21.8h, v28.8h
sqrdmulh v28.8h, v24.8h, v0.h[3]
sub v5.8h, v31.8h, v25.8h
mul v24.8h, v24.8h, v0.h[2]
add v25.8h, v31.8h, v25.8h
sqrdmulh v31.8h, v23.8h, v0.h[5]
mul v23.8h, v23.8h, v0.h[4]
mls v18.8h, v26.8h, v0.h[0]
sqrdmulh v26.8h, v21.8h, v0.h[5]
mul v21.8h, v21.8h, v0.h[4]
mls v22.8h, v19.8h, v0.h[0]
sqrdmulh v19.8h, v30.8h, v0.h[7]
mul v30.8h, v30.8h, v0.h[6]
mls v24.8h, v28.8h, v0.h[0]
sub v28.8h, v27.8h, v18.8h
mls v23.8h, v31.8h, v0.h[0]
add v31.8h, v27.8h, v18.8h
sqrdmulh v18.8h, v6.8h, v0.h[7]
sub v27.8h, v7.8h, v4.8h
mul v6.8h, v6.8h, v0.h[6]
add v4.8h, v7.8h, v4.8h
sqrdmulh v7.8h, v25.8h, v1.h[1]
mul v25.8h, v25.8h, v1.h[0]
mls v21.8h, v26.8h, v0.h[0]
sub v26.8h, v17.8h, v22.8h
mls v30.8h, v19.8h, v0.h[0]
add v19.8h, v17.8h, v22.8h
sqrdmulh v22.8h, v5.8h, v1.h[3]
sub v17.8h, v16.8h, v24.8h
mul v5.8h, v5.8h, v1.h[2]
add v16.8h, v16.8h, v24.8h
mls v6.8h, v18.8h, v0.h[0]
sub v24.8h, v31.8h, v23.8h
sqrdmulh v18.8h, v29.8h, v0.h[3]
add v23.8h, v31.8h, v23.8h
mul v31.8h, v29.8h, v0.h[2]
sub v29.8h, v19.8h, v21.8h
mls v25.8h, v7.8h, v0.h[0]
add v21.8h, v19.8h, v21.8h
mls v5.8h, v22.8h, v0.h[0]
sub v19.8h, v28.8h, v30.8h
sqrdmulh v22.8h, v16.8h, v0.h[5]
add v28.8h, v28.8h, v30.8h
mul v30.8h, v16.8h, v0.h[4]
sub v16.8h, v26.8h, v6.8h
sqrdmulh v7.8h, v17.8h, v0.h[7]
add v26.8h, v26.8h, v6.8h
mul v17.8h, v17.8h, v0.h[6]
sub v6.8h, v23.8h, v25.8h
mls v31.8h, v18.8h, v0.h[0]
add v18.8h, v23.8h, v25.8h
sqrdmulh v25.8h, v21.8h, v1.h[1]
sub v23.8h, v24.8h, v5.8h
mul v21.8h, v21.8h, v1.h[0]
add v24.8h, v24.8h, v5.8h
sqrdmulh v5.8h, v29.8h, v1.h[3]
mul v29.8h, v29.8h, v1.h[2]
mls v30.8h, v22.8h, v0.h[0]
sub v22.8h, v20.8h, v31.8h
mls v17.8h, v7.8h, v0.h[0]
add v20.8h, v20.8h, v31.8h
sqrdmulh v31.8h, v4.8h, v1.h[5]
mul v7.8h, v4.8h, v1.h[4]
sqrdmulh v4.8h, v27.8h, v1.h[7]
mul v27.8h, v27.8h, v1.h[6]
mls v21.8h, v25.8h, v0.h[0]
sub v25.8h, v20.8h, v30.8h
mls v7.8h, v31.8h, v0.h[0]
add v31.8h, v20.8h, v30.8h
sqrdmulh v20.8h, v26.8h, v1.h[5]
add v30.8h, v22.8h, v17.8h
mls v27.8h, v4.8h, v0.h[0]
sub v17.8h, v22.8h, v17.8h
mul v22.8h, v26.8h, v1.h[4]
sub v26.8h, v31.8h, v21.8h
sub v4.8h, v28.8h, v7.8h
add v28.8h, v28.8h, v7.8h
sqrdmulh v7.8h, v16.8h, v1.h[7]
add v31.8h, v31.8h, v21.8h
mul v21.8h, v16.8h, v1.h[6]
sub v16.8h, v19.8h, v27.8h
add v19.8h, v19.8h, v27.8h
sqrdmulh v27.8h, v18.8h, v2.h[1]
mul v18.8h, v18.8h, v2.h[0]
sqrdmulh v1.8h, v6.8h, v2.h[3]
mul v6.8h, v6.8h, v2.h[2]
mls v29.8h, v5.8h, v0.h[0]
sqrdmulh v5.8h, v24.8h, v2.h[5]
mul v24.8h, v24.8h, v2.h[4]
mls v22.8h, v20.8h, v0.h[0]
sqrdmulh v20.8h, v23.8h, v2.h[7]
mul v23.8h, v23.8h, v2.h[6]
sub v2.8h, v25.8h, v29.8h
mls v21.8h, v7.8h, v0.h[0]
add v29.8h, v25.8h, v29.8h
sqrdmulh v25.8h, v28.8h, v3.h[1]
sub v7.8h, v30.8h, v22.8h
mul v28.8h, v28.8h, v3.h[0]
add v22.8h, v30.8h, v22.8h
sqrdmulh v30.8h, v4.8h, v3.h[3]
mul v4.8h, v4.8h, v3.h[2]
mls v18.8h, v27.8h, v0.h[0]
sub v27.8h, v17.8h, v21.8h
mls v6.8h, v1.8h, v0.h[0]
add v17.8h, v17.8h, v21.8h
sqrdmulh v21.8h, v19.8h, v3.h[5]
mul v19.8h, v19.8h, v3.h[4]
sqrdmulh v1.8h, v16.8h, v3.h[7]
mul v16.8h, v16.8h, v3.h[6]
sub v3.8h, v31.8h, v18.8h
mls v24.8h, v5.8h, v0.h[0]
add v31.8h, v31.8h, v18.8h
mls v23.8h, v20.8h, v0.h[0]
sub v18.8h, v26.8h, v6.8h
str q3, [x0, #48]
mls v28.8h, v25.8h, v0.h[0]
add v20.8h, v26.8h, v6.8h
str q31, [x0, #16]
ldr q5, [x2, #64]
ldr q3, [x2, #80]
mls v4.8h, v30.8h, v0.h[0]
str q18, [x0, #112]
ldr q6, [x2, #96]
ldr q25, [x0, #16]
mls v19.8h, v21.8h, v0.h[0]
add v26.8h, v29.8h, v24.8h
str q20, [x0, #80]
ldr q31, [x0, #48]
mls v16.8h, v1.8h, v0.h[0]
sub v30.8h, v29.8h, v24.8h
ldr q0, [x2, #112]
ldr q1, [x2, #128]
ldr q18, [x0, #0]
sub v21.8h, v2.8h, v23.8h
add v20.8h, v2.8h, v23.8h
str q26, [x0, #144]
ldr q24, [x0, #32]
add v29.8h, v22.8h, v28.8h
sub v23.8h, v22.8h, v28.8h
str q30, [x0, #176]
ldr q26, [x2, #144]
sub v28.8h, v7.8h, v4.8h
add v22.8h, v7.8h, v4.8h
str q20, [x0, #208]
str q21, [x0, #240]
ldr q30, [x2, #160]
ldr q20, [x2, #208]
sub v21.8h, v17.8h, v19.8h
add v19.8h, v17.8h, v19.8h
str q29, [x0, #272]
str q23, [x0, #304]
ldr q17, [x0, #80]
ldr q29, [x0, #64]
sub v23.8h, v27.8h, v16.8h
add v16.8h, v27.8h, v16.8h
str q28, [x0, #368]
str q22, [x0, #336]
ldr q27, [x2, #224]
ldr q28, [x2, #176]
str q21, [x0, #432]
str q19, [x0, #400]
sqrdmulh v22.8h, v25.8h, v5.h[1]
ldr q21, [x2, #272]
str q16, [x0, #464]
str q23, [x0, #496]
mul v19.8h, v25.8h, v5.h[0]
ldr q16, [x2, #288]
ldr q23, [x2, #192]
sqrdmulh v25.8h, v31.8h, v5.h[3]
mul v31.8h, v31.8h, v5.h[2]
sqrdmulh v2.8h, v17.8h, v5.h[5]
mul v17.8h, v17.8h, v5.h[4]
mls v19.8h, v22.8h, v1.h[0]
mls v31.8h, v25.8h, v1.h[0]
mls v17.8h, v2.8h, v1.h[0]
ldr q22, [x2, #240]
sub v25.8h, v18.8h, v19.8h
add v18.8h, v18.8h, v19.8h
sub v19.8h, v24.8h, v31.8h
add v24.8h, v24.8h, v31.8h
trn2 v31.2d, v18.2d, v25.2d
trn1 v25.2d, v18.2d, v25.2d
sub v18.8h, v29.8h, v17.8h
add v29.8h, v29.8h, v17.8h
trn2 v17.2d, v24.2d, v19.2d
sqrdmulh v30.8h, v31.8h, v30.8h
trn2 v7.2d, v29.2d, v18.2d
mul v31.8h, v31.8h, v26.8h
sqrdmulh v26.8h, v17.8h, v27.8h
trn1 v27.2d, v24.2d, v19.2d
mul v24.8h, v17.8h, v20.8h
ldr q19, [x2, #256]
trn1 v17.2d, v29.2d, v18.2d
ldr q20, [x2, #304]
sqrdmulh v18.8h, v7.8h, v16.8h
mul v29.8h, v7.8h, v21.8h
ldr q16, [x2, #320]
mls v31.8h, v30.8h, v1.h[0]
ldr q21, [x0, #112]
mls v24.8h, v26.8h, v1.h[0]
ldr q30, [x0, #96]
mls v29.8h, v18.8h, v1.h[0]
sub v26.8h, v25.8h, v31.8h
add v18.8h, v25.8h, v31.8h
ldr q25, [x2, #336]
sub v31.8h, v27.8h, v24.8h
add v27.8h, v27.8h, v24.8h
trn2 v24.4s, v18.4s, v26.4s
trn1 v18.4s, v18.4s, v26.4s
sqrdmulh v26.8h, v21.8h, v5.h[7]
sub v4.8h, v17.8h, v29.8h
mul v21.8h, v21.8h, v5.h[6]
add v29.8h, v17.8h, v29.8h
trn2 v17.4s, v27.4s, v31.4s
sqrdmulh v23.8h, v24.8h, v23.8h
trn2 v2.4s, v29.4s, v4.4s
mul v24.8h, v24.8h, v28.8h
sqrdmulh v28.8h, v17.8h, v19.8h
trn1 v19.4s, v27.4s, v31.4s
mls v21.8h, v26.8h, v1.h[0]
ldr q31, [x2, #352]
trn1 v27.4s, v29.4s, v4.4s
mul v26.8h, v17.8h, v22.8h
sqrdmulh v29.8h, v2.8h, v16.8h
mul v17.8h, v2.8h, v20.8h
sub v22.8h, v30.8h, v21.8h
add v16.8h, v30.8h, v21.8h
mls v24.8h, v23.8h, v1.h[0]
trn2 v20.2d, v16.2d, v22.2d
trn1 v21.2d, v16.2d, v22.2d
mls v26.8h, v28.8h, v1.h[0]
sqrdmulh v30.8h, v20.8h, v31.8h
mul v23.8h, v20.8h, v25.8h
sub v22.8h, v18.8h, v24.8h
ldr q16, [x2, #368]
mls v17.8h, v29.8h, v1.h[0]
add v28.8h, v18.8h, v24.8h
ldr q31, [x2, #384]
sub v20.8h, v19.8h, v26.8h
add v25.8h, v19.8h, v26.8h
sqrdmulh v29.8h, v28.8h, v1.h[1]
mls v23.8h, v30.8h, v1.h[0]
sub v18.8h, v27.8h, v17.8h
add v24.8h, v27.8h, v17.8h
sqrdmulh v26.8h, v22.8h, v1.h[1]
sqrdmulh v19.8h, v25.8h, v1.h[1]
sshr v30.8h, v29.8h, #11
sub v17.8h, v21.8h, v23.8h
add v27.8h, v21.8h, v23.8h
sqrdmulh v29.8h, v20.8h, v1.h[1]
trn2 v23.4s, v27.4s, v17.4s
trn1 v21.4s, v27.4s, v17.4s
sqrdmulh v17.8h, v24.8h, v1.h[1]
sshr v27.8h, v26.8h, #11
sqrdmulh v26.8h, v23.8h, v31.8h
sshr v31.8h, v19.8h, #11
mul v19.8h, v23.8h, v16.8h
sshr v23.8h, v29.8h, #11
sqrdmulh v16.8h, v18.8h, v1.h[1]
sshr v29.8h, v17.8h, #11
mls v28.8h, v30.8h, v1.h[0]
mls v22.8h, v27.8h, v1.h[0]
mls v19.8h, v26.8h, v1.h[0]
sshr v17.8h, v16.8h, #11
mls v25.8h, v31.8h, v1.h[0]
mls v20.8h, v23.8h, v1.h[0]
mls v24.8h, v29.8h, v1.h[0]
zip1 v30.4s, v28.4s, v22.4s
sub v27.8h, v21.8h, v19.8h
add v26.8h, v21.8h, v19.8h
mls v18.8h, v17.8h, v1.h[0]
zip2 v16.4s, v28.4s, v22.4s
str q30, [x0, #0]
sqrdmulh v31.8h, v26.8h, v1.h[1]
zip1 v23.4s, v25.4s, v20.4s
sqrdmulh v29.8h, v27.8h, v1.h[1]
zip2 v19.4s, v25.4s, v20.4s
str q16, [x0, #16]
ldr q21, [x0, #144]
ldr q17, [x0, #128]
ldr q28, [x2, #400]
str q23, [x0, #32]
ldr q22, [x2, #416]
ldr q30, [x2, #432]
ldr q20, [x2, #448]
zip1 v25.4s, v24.4s, v18.4s
zip2 v16.4s, v24.4s, v18.4s
str q19, [x0, #48]
ldr q23, [x0, #176]
ldr q18, [x0, #160]
ldr q24, [x2, #464]
sshr v19.8h, v31.8h, #11
ldr q31, [x2, #480]
sshr v29.8h, v29.8h, #11
str q25, [x0, #64]
str q16, [x0, #80]
ldr q25, [x0, #208]
ldr q16, [x0, #192]
mls v26.8h, v19.8h, v1.h[0]
ldr q19, [x2, #528]
mls v27.8h, v29.8h, v1.h[0]
sqrdmulh v29.8h, v21.8h, v3.h[1]
mul v21.8h, v21.8h, v3.h[0]
sqrdmulh v7.8h, v23.8h, v3.h[3]
mul v23.8h, v23.8h, v3.h[2]
zip1 v5.4s, v26.4s, v27.4s
sqrdmulh v4.8h, v25.8h, v3.h[5]
zip2 v27.4s, v26.4s, v27.4s
mul v26.8h, v25.8h, v3.h[4]
str q5, [x0, #96]
mls v21.8h, v29.8h, v1.h[0]
str q27, [x0, #112]
mls v23.8h, v7.8h, v1.h[0]
ldr q25, [x2, #544]
ldr q29, [x2, #496]
mls v26.8h, v4.8h, v1.h[0]
ldr q27, [x2, #512]
sub v2.8h, v17.8h, v21.8h
add v21.8h, v17.8h, v21.8h
sub v17.8h, v18.8h, v23.8h
add v23.8h, v18.8h, v23.8h
trn2 v18.2d, v21.2d, v2.2d
trn1 v21.2d, v21.2d, v2.2d
sub v5.8h, v16.8h, v26.8h
add v26.8h, v16.8h, v26.8h
trn2 v16.2d, v23.2d, v17.2d
sqrdmulh v22.8h, v18.8h, v22.8h
trn2 v7.2d, v26.2d, v5.2d
mul v18.8h, v18.8h, v28.8h
sqrdmulh v28.8h, v16.8h, v31.8h
trn1 v31.2d, v23.2d, v17.2d
mul v17.8h, v16.8h, v24.8h
trn1 v23.2d, v26.2d, v5.2d
ldr q16, [x2, #560]
ldr q24, [x2, #576]
sqrdmulh v26.8h, v7.8h, v25.8h
mul v25.8h, v7.8h, v19.8h
ldr q19, [x0, #240]
mls v18.8h, v22.8h, v1.h[0]
ldr q22, [x0, #224]
mls v17.8h, v28.8h, v1.h[0]
mls v25.8h, v26.8h, v1.h[0]
sub v28.8h, v21.8h, v18.8h
add v26.8h, v21.8h, v18.8h
ldr q18, [x2, #592]
ldr q21, [x2, #608]
sub v4.8h, v31.8h, v17.8h
add v17.8h, v31.8h, v17.8h
sqrdmulh v31.8h, v19.8h, v3.h[7]
trn2 v2.4s, v26.4s, v28.4s
mul v19.8h, v19.8h, v3.h[6]
sub v5.8h, v23.8h, v25.8h
add v25.8h, v23.8h, v25.8h
trn2 v23.4s, v17.4s, v4.4s
sqrdmulh v20.8h, v2.8h, v20.8h
trn1 v28.4s, v26.4s, v28.4s
trn2 v26.4s, v25.4s, v5.4s
mul v30.8h, v2.8h, v30.8h
mls v19.8h, v31.8h, v1.h[0]
trn1 v31.4s, v17.4s, v4.4s
sqrdmulh v17.8h, v23.8h, v27.8h
trn1 v27.4s, v25.4s, v5.4s
mul v25.8h, v23.8h, v29.8h
sqrdmulh v29.8h, v26.8h, v24.8h
sub v23.8h, v22.8h, v19.8h
add v24.8h, v22.8h, v19.8h
mul v22.8h, v26.8h, v16.8h
trn2 v19.2d, v24.2d, v23.2d
trn1 v26.2d, v24.2d, v23.2d
mls v30.8h, v20.8h, v1.h[0]
sqrdmulh v16.8h, v19.8h, v21.8h
mul v23.8h, v19.8h, v18.8h
mls v25.8h, v17.8h, v1.h[0]
mls v22.8h, v29.8h, v1.h[0]
sub v24.8h, v28.8h, v30.8h
ldr q20, [x2, #624]
add v21.8h, v28.8h, v30.8h
mls v23.8h, v16.8h, v1.h[0]
ldr q19, [x2, #640]
sub v18.8h, v31.8h, v25.8h
add v17.8h, v31.8h, v25.8h
sub v29.8h, v27.8h, v22.8h
add v30.8h, v27.8h, v22.8h
sqrdmulh v28.8h, v21.8h, v1.h[1]
sub v16.8h, v26.8h, v23.8h
add v25.8h, v26.8h, v23.8h
sqrdmulh v31.8h, v24.8h, v1.h[1]
trn2 v22.4s, v25.4s, v16.4s
trn1 v27.4s, v25.4s, v16.4s
sqrdmulh v23.8h, v17.8h, v1.h[1]
sshr v26.8h, v28.8h, #11
sqrdmulh v16.8h, v22.8h, v19.8h
mul v25.8h, v22.8h, v20.8h
sshr v28.8h, v31.8h, #11
sqrdmulh v19.8h, v18.8h, v1.h[1]
sqrdmulh v22.8h, v30.8h, v1.h[1]
sshr v20.8h, v23.8h, #11
sqrdmulh v31.8h, v29.8h, v1.h[1]
mls v21.8h, v26.8h, v1.h[0]
mls v25.8h, v16.8h, v1.h[0]
sshr v23.8h, v19.8h, #11
sshr v26.8h, v22.8h, #11
mls v24.8h, v28.8h, v1.h[0]
sshr v16.8h, v31.8h, #11
mls v17.8h, v20.8h, v1.h[0]
mls v18.8h, v23.8h, v1.h[0]
sub v19.8h, v27.8h, v25.8h
add v22.8h, v27.8h, v25.8h
mls v30.8h, v26.8h, v1.h[0]
zip1 v28.4s, v21.4s, v24.4s
sqrdmulh v31.8h, v22.8h, v1.h[1]
zip2 v20.4s, v21.4s, v24.4s
mls v29.8h, v16.8h, v1.h[0]
zip1 v23.4s, v17.4s, v18.4s
str q28, [x0, #128]
sqrdmulh v27.8h, v19.8h, v1.h[1]
zip2 v25.4s, v17.4s, v18.4s
str q20, [x0, #144]
ldr q26, [x0, #272]
ldr q21, [x0, #256]
ldr q24, [x2, #656]
str q23, [x0, #160]
ldr q16, [x2, #672]
ldr q28, [x2, #688]
ldr q17, [x2, #704]
sshr v18.8h, v31.8h, #11
str q25, [x0, #176]
ldr q20, [x0, #304]
ldr q23, [x0, #288]
ldr q31, [x2, #720]
zip1 v25.4s, v30.4s, v29.4s
zip2 v30.4s, v30.4s, v29.4s
ldr q29, [x2, #736]
ldr q7, [x2, #752]
sshr v27.8h, v27.8h, #11
mls v22.8h, v18.8h, v1.h[0]
ldr q18, [x2, #768]
str q25, [x0, #192]
str q30, [x0, #208]
ldr q25, [x0, #336]
ldr q30, [x0, #320]
mls v19.8h, v27.8h, v1.h[0]
sqrdmulh v27.8h, v26.8h, v6.h[1]
mul v26.8h, v26.8h, v6.h[0]
sqrdmulh v3.8h, v20.8h, v6.h[3]
mul v20.8h, v20.8h, v6.h[2]
zip1 v2.4s, v22.4s, v19.4s
zip2 v22.4s, v22.4s, v19.4s
sqrdmulh v19.8h, v25.8h, v6.h[5]
str q2, [x0, #224]
mul v25.8h, v25.8h, v6.h[4]
str q22, [x0, #240]
mls v26.8h, v27.8h, v1.h[0]
ldr q22, [x2, #784]
mls v20.8h, v3.8h, v1.h[0]
ldr q27, [x2, #800]
mls v25.8h, v19.8h, v1.h[0]
ldr q19, [x2, #816]
sub v4.8h, v21.8h, v26.8h
add v21.8h, v21.8h, v26.8h
sub v26.8h, v23.8h, v20.8h
add v23.8h, v23.8h, v20.8h
trn2 v20.2d, v21.2d, v4.2d
trn1 v21.2d, v21.2d, v4.2d
sub v5.8h, v30.8h, v25.8h
add v30.8h, v30.8h, v25.8h
trn2 v25.2d, v23.2d, v26.2d
sqrdmulh v16.8h, v20.8h, v16.8h
trn2 v2.2d, v30.2d, v5.2d
mul v20.8h, v20.8h, v24.8h
sqrdmulh v24.8h, v25.8h, v29.8h
trn1 v29.2d, v23.2d, v26.2d
mul v23.8h, v25.8h, v31.8h
trn1 v26.2d, v30.2d, v5.2d
ldr q25, [x2, #832]
ldr q31, [x0, #368]
sqrdmulh v30.8h, v2.8h, v27.8h
mul v27.8h, v2.8h, v22.8h
ldr q22, [x0, #352]
mls v20.8h, v16.8h, v1.h[0]
mls v23.8h, v24.8h, v1.h[0]
mls v27.8h, v30.8h, v1.h[0]
sqrdmulh v16.8h, v31.8h, v6.h[7]
sub v24.8h, v21.8h, v20.8h
mul v30.8h, v31.8h, v6.h[6]
ldr q31, [x2, #848]
add v21.8h, v21.8h, v20.8h
ldr q20, [x2, #864]
sub v3.8h, v29.8h, v23.8h
add v29.8h, v29.8h, v23.8h
sub v23.8h, v26.8h, v27.8h
add v27.8h, v26.8h, v27.8h
trn2 v26.4s, v21.4s, v24.4s
trn2 v4.4s, v29.4s, v3.4s
mls v30.8h, v16.8h, v1.h[0]
trn2 v16.4s, v27.4s, v23.4s
sqrdmulh v17.8h, v26.8h, v17.8h
trn1 v21.4s, v21.4s, v24.4s
mul v24.8h, v26.8h, v28.8h
trn1 v26.4s, v29.4s, v3.4s
sqrdmulh v28.8h, v4.8h, v18.8h
trn1 v29.4s, v27.4s, v23.4s
sub v18.8h, v22.8h, v30.8h
add v23.8h, v22.8h, v30.8h
mul v27.8h, v4.8h, v7.8h
trn2 v30.2d, v23.2d, v18.2d
trn1 v22.2d, v23.2d, v18.2d
sqrdmulh v18.8h, v16.8h, v25.8h
sqrdmulh v23.8h, v30.8h, v20.8h
mul v25.8h, v30.8h, v31.8h
mul v20.8h, v16.8h, v19.8h
mls v24.8h, v17.8h, v1.h[0]
mls v27.8h, v28.8h, v1.h[0]
mls v25.8h, v23.8h, v1.h[0]
mls v20.8h, v18.8h, v1.h[0]
sub v30.8h, v21.8h, v24.8h
add v31.8h, v21.8h, v24.8h
ldr q16, [x2, #880]
ldr q19, [x2, #896]
sub v17.8h, v26.8h, v27.8h
add v28.8h, v26.8h, v27.8h
sub v23.8h, v22.8h, v25.8h
add v18.8h, v22.8h, v25.8h
sub v21.8h, v29.8h, v20.8h
add v24.8h, v29.8h, v20.8h
trn2 v27.4s, v18.4s, v23.4s
trn1 v26.4s, v18.4s, v23.4s
sqrdmulh v25.8h, v31.8h, v1.h[1]
sqrdmulh v22.8h, v24.8h, v1.h[1]
sqrdmulh v20.8h, v27.8h, v19.8h
sqrdmulh v29.8h, v21.8h, v1.h[1]
sqrdmulh v23.8h, v30.8h, v1.h[1]
sshr v18.8h, v25.8h, #11
mul v19.8h, v27.8h, v16.8h
sshr v25.8h, v22.8h, #11
sqrdmulh v27.8h, v28.8h, v1.h[1]
sqrdmulh v16.8h, v17.8h, v1.h[1]
sshr v22.8h, v29.8h, #11
sshr v29.8h, v23.8h, #11
mls v24.8h, v25.8h, v1.h[0]
mls v21.8h, v22.8h, v1.h[0]
sshr v23.8h, v27.8h, #11
mls v31.8h, v18.8h, v1.h[0]
mls v19.8h, v20.8h, v1.h[0]
sshr v25.8h, v16.8h, #11
mls v30.8h, v29.8h, v1.h[0]
mls v28.8h, v23.8h, v1.h[0]
zip1 v22.4s, v24.4s, v21.4s
mls v17.8h, v25.8h, v1.h[0]
zip2 v27.4s, v24.4s, v21.4s
sub v18.8h, v26.8h, v19.8h
add v20.8h, v26.8h, v19.8h
str q22, [x0, #320]
zip1 v16.4s, v31.4s, v30.4s
zip2 v29.4s, v31.4s, v30.4s
str q27, [x0, #336]
sqrdmulh v23.8h, v20.8h, v1.h[1]
zip1 v25.4s, v28.4s, v17.4s
zip2 v21.4s, v28.4s, v17.4s
str q16, [x0, #256]
str q29, [x0, #272]
ldr q24, [x0, #400]
ldr q19, [x0, #384]
ldr q26, [x2, #912]
sqrdmulh v22.8h, v18.8h, v1.h[1]
ldr q31, [x2, #928]
ldr q30, [x2, #944]
ldr q27, [x2, #960]
str q25, [x0, #288]
str q21, [x0, #304]
ldr q17, [x0, #432]
ldr q28, [x0, #464]
ldr q16, [x0, #416]
sshr v29.8h, v23.8h, #11
ldr q25, [x0, #448]
ldr q21, [x2, #976]
ldr q23, [x2, #992]
ldr q5, [x2, #1040]
ldr q2, [x2, #1056]
sshr v22.8h, v22.8h, #11
mls v20.8h, v29.8h, v1.h[0]
ldr q29, [x2, #1008]
sqrdmulh v6.8h, v24.8h, v0.h[1]
mul v24.8h, v24.8h, v0.h[0]
sqrdmulh v3.8h, v17.8h, v0.h[3]
mul v17.8h, v17.8h, v0.h[2]
sqrdmulh v4.8h, v28.8h, v0.h[5]
mul v28.8h, v28.8h, v0.h[4]
mls v24.8h, v6.8h, v1.h[0]
mls v17.8h, v3.8h, v1.h[0]
mls v18.8h, v22.8h, v1.h[0]
mls v28.8h, v4.8h, v1.h[0]
ldr q22, [x2, #1024]
sub v7.8h, v19.8h, v24.8h
add v24.8h, v19.8h, v24.8h
sub v19.8h, v16.8h, v17.8h
add v17.8h, v16.8h, v17.8h
trn2 v16.2d, v24.2d, v7.2d
trn1 v24.2d, v24.2d, v7.2d
sub v6.8h, v25.8h, v28.8h
add v28.8h, v25.8h, v28.8h
trn2 v25.2d, v17.2d, v19.2d
sqrdmulh v31.8h, v16.8h, v31.8h
trn2 v3.2d, v28.2d, v6.2d
mul v16.8h, v16.8h, v26.8h
sqrdmulh v26.8h, v25.8h, v23.8h
trn1 v23.2d, v17.2d, v19.2d
mul v19.8h, v25.8h, v21.8h
trn1 v17.2d, v28.2d, v6.2d
ldr q25, [x2, #1072]
ldr q21, [x2, #1088]
sqrdmulh v28.8h, v3.8h, v2.8h
zip1 v4.4s, v20.4s, v18.4s
mul v7.8h, v3.8h, v5.8h
zip2 v18.4s, v20.4s, v18.4s
mls v16.8h, v31.8h, v1.h[0]
str q4, [x0, #352]
mls v19.8h, v26.8h, v1.h[0]
str q18, [x0, #368]
ldr q20, [x0, #496]
ldr q31, [x0, #480]
mls v7.8h, v28.8h, v1.h[0]
sub v26.8h, v24.8h, v16.8h
add v18.8h, v24.8h, v16.8h
ldr q28, [x2, #1104]
ldr q16, [x2, #1120]
sub v24.8h, v23.8h, v19.8h
add v19.8h, v23.8h, v19.8h
trn2 v23.4s, v18.4s, v26.4s
trn1 v26.4s, v18.4s, v26.4s
sub v18.8h, v17.8h, v7.8h
add v17.8h, v17.8h, v7.8h
sqrdmulh v6.8h, v20.8h, v0.h[7]
trn2 v2.4s, v19.4s, v24.4s
mul v20.8h, v20.8h, v0.h[6]
trn2 v5.4s, v17.4s, v18.4s
sqrdmulh v27.8h, v23.8h, v27.8h
trn1 v24.4s, v19.4s, v24.4s
mul v19.8h, v23.8h, v30.8h
trn1 v23.4s, v17.4s, v18.4s
sqrdmulh v30.8h, v2.8h, v22.8h
mls v20.8h, v6.8h, v1.h[0]
mul v18.8h, v2.8h, v29.8h
sqrdmulh v17.8h, v5.8h, v21.8h
mul v22.8h, v5.8h, v25.8h
sub v29.8h, v31.8h, v20.8h
add v21.8h, v31.8h, v20.8h
mls v19.8h, v27.8h, v1.h[0]
trn2 v25.2d, v21.2d, v29.2d
trn1 v31.2d, v21.2d, v29.2d
mls v18.8h, v30.8h, v1.h[0]
sqrdmulh v20.8h, v25.8h, v16.8h
mul v27.8h, v25.8h, v28.8h
sub v29.8h, v26.8h, v19.8h
ldr q21, [x2, #1136]
mls v22.8h, v17.8h, v1.h[0]
add v30.8h, v26.8h, v19.8h
ldr q16, [x2, #1152]
sub v25.8h, v24.8h, v18.8h
add v28.8h, v24.8h, v18.8h
sqrdmulh v17.8h, v30.8h, v1.h[1]
mls v27.8h, v20.8h, v1.h[0]
sub v19.8h, v23.8h, v22.8h
add v26.8h, v23.8h, v22.8h
sqrdmulh v18.8h, v29.8h, v1.h[1]
sqrdmulh v24.8h, v28.8h, v1.h[1]
sshr v20.8h, v17.8h, #11
sub v22.8h, v31.8h, v27.8h
add v23.8h, v31.8h, v27.8h
sqrdmulh v17.8h, v25.8h, v1.h[1]
trn2 v27.4s, v23.4s, v22.4s
trn1 v31.4s, v23.4s, v22.4s
sqrdmulh v22.8h, v26.8h, v1.h[1]
sshr v23.8h, v18.8h, #11
sqrdmulh v18.8h, v27.8h, v16.8h
sshr v16.8h, v24.8h, #11
mul v24.8h, v27.8h, v21.8h
sshr v27.8h, v17.8h, #11
sqrdmulh v21.8h, v19.8h, v1.h[1]
sshr v17.8h, v22.8h, #11
mls v30.8h, v20.8h, v1.h[0]
mls v29.8h, v23.8h, v1.h[0]
mls v24.8h, v18.8h, v1.h[0]
sshr v22.8h, v21.8h, #11
mls v26.8h, v17.8h, v1.h[0]
mls v28.8h, v16.8h, v1.h[0]
mls v19.8h, v22.8h, v1.h[0]
zip1 v20.4s, v30.4s, v29.4s
sub v23.8h, v31.8h, v24.8h
add v18.8h, v31.8h, v24.8h
mls v25.8h, v27.8h, v1.h[0]
zip2 v21.4s, v30.4s, v29.4s
str q20, [x0, #384]
sqrdmulh v17.8h, v18.8h, v1.h[1]
sqrdmulh v16.8h, v23.8h, v1.h[1]
zip1 v22.4s, v26.4s, v19.4s
str q21, [x0, #400]
zip2 v31.4s, v26.4s, v19.4s
zip1 v24.4s, v28.4s, v25.4s
zip2 v27.4s, v28.4s, v25.4s
str q22, [x0, #448]
sshr v30.8h, v17.8h, #11
str q31, [x0, #464]
sshr v29.8h, v16.8h, #11
str q24, [x0, #416]
str q27, [x0, #432]
mls v18.8h, v30.8h, v1.h[0]
mls v23.8h, v29.8h, v1.h[0]
zip1 v20.4s, v18.4s, v23.4s
zip2 v21.4s, v18.4s, v23.4s
str q20, [x0, #480]
str q21, [x0, #496]
ret
.section .rodata
.p2align 4
cr_fwd_ls_t:
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
.globl cr_inv_ls
.p2align 4
cr_inv_ls:
adrp x2, cr_inv_ls_t
add x2, x2, :lo12:cr_inv_ls_t
ldr q16, [x0, #0]
ldr q17, [x0, #16]
ldr q18, [x0, #32]
ldr q19, [x0, #48]
ldr q20, [x2, #80]
ldr q21, [x2, #96]
ldr q22, [x2, #144]
ldr q23, [x2, #160]
ldr q0, [x2, #64]
ldr q24, [x2, #112]
ldr q25, [x2, #128]
ldr q1, [x2, #0]
ldr q2, [x2, #16]
ldr q3, [x2, #32]
ldr q4, [x2, #48]
ldr q26, [x0, #64]
ldr q27, [x0, #80]
ldr q28, [x2, #208]
uzp1 v29.4s, v16.4s, v17.4s
uzp2 v30.4s, v16.4s, v17.4s
ldr q31, [x2, #224]
ldr q16, [x2, #176]
ldr q17, [x2, #192]
uzp1 v5.4s, v18.4s, v19.4s
uzp2 v18.4s, v18.4s, v19.4s
ldr q19, [x2, #240]
sub v6.8h, v30.8h, v29.8h
add v30.8h, v29.8h, v30.8h
sub v29.8h, v18.8h, v5.8h
add v18.8h, v5.8h, v18.8h
sqrdmulh v21.8h, v6.8h, v21.8h
mul v20.8h, v6.8h, v20.8h
uzp1 v7.4s, v26.4s, v27.4s
uzp2 v26.4s, v26.4s, v27.4s
sqrdmulh v27.8h, v29.8h, v23.8h
ldr q23, [x2, #256]
mul v22.8h, v29.8h, v22.8h
ldr q29, [x0, #96]
sub v5.8h, v26.8h, v7.8h
add v26.8h, v7.8h, v26.8h
mls v20.8h, v21.8h, v0.h[0]
ldr q21, [x0, #112]
sqrdmulh v31.8h, v5.8h, v31.8h
mul v28.8h, v5.8h, v28.8h
ldr q6, [x2, #272]
mls v22.8h, v27.8h, v0.h[0]
ldr q27, [x2, #288]
trn1 v7.4s, v30.4s, v20.4s
trn2 v30.4s, v30.4s, v20.4s
sub v20.8h, v30.8h, v7.8h
add v30.8h, v7.8h, v30.8h
mls v28.8h, v31.8h, v0.h[0]
trn1 v31.4s, v18.4s, v22.4s
sqrdmulh v25.8h, v20.8h, v25.8h
trn2 v22.4s, v18.4s, v22.4s
ldr q18, [x2, #304]
mul v24.8h, v20.8h, v24.8h
uzp1 v20.4s, v29.4s, v21.4s
sub v5.8h, v22.8h, v31.8h
add v31.8h, v31.8h, v22.8h
trn1 v22.4s, v26.4s, v28.4s
trn2 v26.4s, v26.4s, v28.4s
sqrdmulh v28.8h, v5.8h, v17.8h
uzp2 v17.4s, v29.4s, v21.4s
ldr q29, [x2, #320]
mls v24.8h, v25.8h, v0.h[0]
sub v21.8h, v26.8h, v22.8h
mul v25.8h, v5.8h, v16.8h
add v16.8h, v22.8h, v26.8h
ldr q22, [x0, #128]
ldr q26, [x0, #144]
sub v7.8h, v17.8h, v20.8h
add v20.8h, v20.8h, v17.8h
sqrdmulh v17.8h, v21.8h, v23.8h
trn1 v23.2d, v30.2d, v24.2d
trn2 v24.2d, v30.2d, v24.2d
mls v25.8h, v28.8h, v0.h[0]
ldr q30, [x2, #336]
sub v28.8h, v24.8h, v23.8h
add v23.8h, v23.8h, v24.8h
sqrdmulh v24.8h, v7.8h, v27.8h
uzp1 v27.4s, v22.4s, v26.4s
sqrdmulh v5.8h, v28.8h, v1.h[1]
str q23, [x0, #0]
uzp2 v23.4s, v22.4s, v26.4s
mul v22.8h, v28.8h, v1.h[0]
trn1 v26.2d, v31.2d, v25.2d
trn2 v28.2d, v31.2d, v25.2d
mul v31.8h, v7.8h, v6.8h
ldr q25, [x2, #352]
mul v19.8h, v21.8h, v19.8h
sub v21.8h, v23.8h, v27.8h
sub v6.8h, v28.8h, v26.8h
add v26.8h, v26.8h, v28.8h
mls v22.8h, v5.8h, v0.h[0]
add v28.8h, v27.8h, v23.8h
sqrdmulh v27.8h, v6.8h, v1.h[3]
str q26, [x0, #32]
mul v23.8h, v6.8h, v1.h[2]
mls v31.8h, v24.8h, v0.h[0]
str q22, [x0, #16]
mls v19.8h, v17.8h, v0.h[0]
ldr q26, [x0, #160]
ldr q24, [x0, #176]
ldr q22, [x2, #400]
sqrdmulh v17.8h, v21.8h, v25.8h
mls v23.8h, v27.8h, v0.h[0]
ldr q25, [x2, #416]
ldr q27, [x2, #368]
ldr q7, [x2, #384]
trn1 v5.4s, v20.4s, v31.4s
trn2 v31.4s, v20.4s, v31.4s
trn1 v20.2d, v16.2d, v19.2d
trn2 v16.2d, v16.2d, v19.2d
sub v19.8h, v31.8h, v5.8h
add v31.8h, v5.8h, v31.8h
str q23, [x0, #48]
sub v23.8h, v16.8h, v20.8h
add v16.8h, v20.8h, v16.8h
sqrdmulh v20.8h, v19.8h, v29.8h
uzp1 v29.4s, v26.4s, v24.4s
mul v18.8h, v19.8h, v18.8h
str q16, [x0, #64]
uzp2 v19.4s, v26.4s, v24.4s
ldr q16, [x0, #192]
ldr q26, [x0, #208]
ldr q24, [x2, #464]
sqrdmulh v6.8h, v23.8h, v1.h[5]
mul v23.8h, v23.8h, v1.h[4]
sub v5.8h, v19.8h, v29.8h
mul v30.8h, v21.8h, v30.8h
add v21.8h, v29.8h, v19.8h
mls v18.8h, v20.8h, v0.h[0]
ldr q29, [x2, #480]
sqrdmulh v19.8h, v5.8h, v25.8h
mls v23.8h, v6.8h, v0.h[0]
uzp1 v20.4s, v16.4s, v26.4s
mul v25.8h, v5.8h, v22.8h
uzp2 v22.4s, v16.4s, v26.4s
ldr q26, [x2, #432]
ldr q16, [x2, #448]
trn1 v6.2d, v31.2d, v18.2d
trn2 v18.2d, v31.2d, v18.2d
mls v30.8h, v17.8h, v0.h[0]
sub v31.8h, v22.8h, v20.8h
sub v17.8h, v18.8h, v6.8h
add v18.8h, v6.8h, v18.8h
str q23, [x0, #80]
sqrdmulh v23.8h, v31.8h, v29.8h
add v29.8h, v20.8h, v22.8h
ldr q20, [x2, #496]
ldr q22, [x2, #512]
sqrdmulh v5.8h, v17.8h, v1.h[7]
str q18, [x0, #96]
mul v18.8h, v17.8h, v1.h[6]
trn1 v17.4s, v28.4s, v30.4s
trn2 v28.4s, v28.4s, v30.4s
mul v30.8h, v31.8h, v24.8h
ldr q24, [x0, #224]
ldr q31, [x0, #240]
mls v25.8h, v19.8h, v0.h[0]
ldr q19, [x2, #528]
sub v6.8h, v28.8h, v17.8h
add v17.8h, v17.8h, v28.8h
mls v18.8h, v5.8h, v0.h[0]
ldr q28, [x2, #544]
sqrdmulh v1.8h, v6.8h, v7.8h
mul v27.8h, v6.8h, v27.8h
trn1 v5.4s, v21.4s, v25.4s
mls v30.8h, v23.8h, v0.h[0]
trn2 v23.4s, v21.4s, v25.4s
str q18, [x0, #112]
uzp1 v21.4s, v24.4s, v31.4s
uzp2 v25.4s, v24.4s, v31.4s
sub v18.8h, v23.8h, v5.8h
add v24.8h, v5.8h, v23.8h
ldr q31, [x0, #256]
ldr q23, [x0, #272]
ldr q7, [x2, #560]
mls v27.8h, v1.8h, v0.h[0]
sub v6.8h, v25.8h, v21.8h
trn1 v5.4s, v29.4s, v30.4s
trn2 v30.4s, v29.4s, v30.4s
sqrdmulh v29.8h, v18.8h, v16.8h
add v16.8h, v21.8h, v25.8h
ldr q21, [x2, #576]
sub v25.8h, v30.8h, v5.8h
mul v26.8h, v18.8h, v26.8h
trn1 v18.2d, v17.2d, v27.2d
trn2 v17.2d, v17.2d, v27.2d
sqrdmulh v27.8h, v25.8h, v22.8h
add v22.8h, v5.8h, v30.8h
ldr q30, [x2, #592]
sub v1.8h, v17.8h, v18.8h
add v18.8h, v18.8h, v17.8h
mul v17.8h, v25.8h, v20.8h
uzp1 v20.4s, v31.4s, v23.4s
sqrdmulh v25.8h, v1.8h, v2.h[1]
str q18, [x0, #128]
uzp2 v18.4s, v31.4s, v23.4s
mul v31.8h, v1.8h, v2.h[0]
ldr q23, [x2, #608]
mls v26.8h, v29.8h, v0.h[0]
sub v29.8h, v18.8h, v20.8h
mls v17.8h, v27.8h, v0.h[0]
add v27.8h, v20.8h, v18.8h
sqrdmulh v18.8h, v6.8h, v28.8h
mls v31.8h, v25.8h, v0.h[0]
trn1 v20.2d, v24.2d, v26.2d
trn2 v28.2d, v24.2d, v26.2d
trn1 v25.2d, v22.2d, v17.2d
mul v24.8h, v6.8h, v19.8h
sub v26.8h, v28.8h, v20.8h
add v19.8h, v20.8h, v28.8h
str q31, [x0, #144]
trn2 v20.2d, v22.2d, v17.2d
sqrdmulh v28.8h, v29.8h, v23.8h
sqrdmulh v31.8h, v26.8h, v2.h[3]
str q19, [x0, #160]
ldr q17, [x0, #288]
ldr q22, [x0, #304]
ldr q23, [x2, #656]
mul v19.8h, v26.8h, v2.h[2]
sub v26.8h, v20.8h, v25.8h
ldr q5, [x2, #672]
mls v24.8h, v18.8h, v0.h[0]
add v18.8h, v25.8h, v20.8h
ldr q25, [x2, #624]
ldr q20, [x2, #640]
sqrdmulh v1.8h, v26.8h, v2.h[5]
mul v26.8h, v26.8h, v2.h[4]
str q18, [x0, #192]
mls v19.8h, v31.8h, v0.h[0]
trn1 v18.4s, v16.4s, v24.4s
trn2 v31.4s, v16.4s, v24.4s
uzp1 v16.4s, v17.4s, v22.4s
uzp2 v24.4s, v17.4s, v22.4s
sub v17.8h, v31.8h, v18.8h
add v22.8h, v18.8h, v31.8h
str q19, [x0, #176]
mls v26.8h, v1.8h, v0.h[0]
sub v18.8h, v24.8h, v16.8h
sqrdmulh v31.8h, v17.8h, v21.8h
add v19.8h, v16.8h, v24.8h
ldr q21, [x2, #688]
ldr q16, [x0, #320]
ldr q24, [x0, #336]
mul v17.8h, v17.8h, v7.8h
ldr q6, [x2, #720]
mul v30.8h, v29.8h, v30.8h
ldr q29, [x2, #736]
str q26, [x0, #208]
sqrdmulh v26.8h, v18.8h, v5.8h
ldr q1, [x2, #704]
mul v23.8h, v18.8h, v23.8h
ldr q18, [x2, #752]
mls v17.8h, v31.8h, v0.h[0]
ldr q31, [x2, #768]
mls v30.8h, v28.8h, v0.h[0]
uzp1 v28.4s, v16.4s, v24.4s
uzp2 v16.4s, v16.4s, v24.4s
ldr q24, [x0, #352]
mls v23.8h, v26.8h, v0.h[0]
ldr q26, [x0, #368]
trn1 v7.2d, v22.2d, v17.2d
trn2 v22.2d, v22.2d, v17.2d
trn1 v17.4s, v27.4s, v30.4s
trn2 v27.4s, v27.4s, v30.4s
sub v30.8h, v22.8h, v7.8h
add v22.8h, v7.8h, v22.8h
trn1 v5.4s, v19.4s, v23.4s
trn2 v23.4s, v19.4s, v23.4s
sqrdmulh v19.8h, v30.8h, v2.h[7]
str q22, [x0, #224]
sub v22.8h, v27.8h, v17.8h
mul v30.8h, v30.8h, v2.h[6]
add v17.8h, v17.8h, v27.8h
ldr q27, [x2, #784]
sqrdmulh v20.8h, v22.8h, v20.8h
sub v7.8h, v16.8h, v28.8h
mul v25.8h, v22.8h, v25.8h
add v22.8h, v28.8h, v16.8h
ldr q28, [x2, #800]
sqrdmulh v16.8h, v7.8h, v29.8h
sub v29.8h, v23.8h, v5.8h
mls v30.8h, v19.8h, v0.h[0]
add v19.8h, v5.8h, v23.8h
mul v23.8h, v7.8h, v6.8h
uzp1 v2.4s, v24.4s, v26.4s
mls v25.8h, v20.8h, v0.h[0]
uzp2 v20.4s, v24.4s, v26.4s
sqrdmulh v24.8h, v29.8h, v1.8h
str q30, [x0, #240]
mul v26.8h, v29.8h, v21.8h
sub v30.8h, v20.8h, v2.8h
mls v23.8h, v16.8h, v0.h[0]
ldr q21, [x0, #384]
ldr q29, [x0, #400]
add v16.8h, v2.8h, v20.8h
ldr q20, [x2, #816]
trn1 v5.2d, v17.2d, v25.2d
trn2 v25.2d, v17.2d, v25.2d
ldr q17, [x2, #832]
ldr q7, [x2, #848]
ldr q6, [x2, #864]
sqrdmulh v28.8h, v30.8h, v28.8h
sub v1.8h, v25.8h, v5.8h
add v25.8h, v5.8h, v25.8h
trn1 v2.4s, v22.4s, v23.4s
trn2 v22.4s, v22.4s, v23.4s
sqrdmulh v23.8h, v1.8h, v3.h[1]
str q25, [x0, #256]
mul v25.8h, v1.8h, v3.h[0]
sub v5.8h, v22.8h, v2.8h
mls v26.8h, v24.8h, v0.h[0]
add v24.8h, v2.8h, v22.8h
sqrdmulh v22.8h, v5.8h, v31.8h
uzp1 v31.4s, v21.4s, v29.4s
mul v18.8h, v5.8h, v18.8h
uzp2 v21.4s, v21.4s, v29.4s
mls v25.8h, v23.8h, v0.h[0]
trn1 v29.2d, v19.2d, v26.2d
trn2 v23.2d, v19.2d, v26.2d
sub v19.8h, v21.8h, v31.8h
mul v26.8h, v30.8h, v27.8h
mls v18.8h, v22.8h, v0.h[0]
sub v27.8h, v23.8h, v29.8h
str q25, [x0, #272]
add v30.8h, v29.8h, v23.8h
sqrdmulh v22.8h, v19.8h, v6.8h
sqrdmulh v25.8h, v27.8h, v3.h[3]
ldr q29, [x0, #416]
ldr q23, [x0, #432]
ldr q1, [x2, #912]
add v31.8h, v31.8h, v21.8h
mul v21.8h, v27.8h, v3.h[2]
str q30, [x0, #288]
ldr q27, [x2, #928]
ldr q30, [x2, #880]
ldr q2, [x2, #896]
trn1 v5.2d, v24.2d, v18.2d
trn2 v24.2d, v24.2d, v18.2d
mls v26.8h, v28.8h, v0.h[0]
sub v18.8h, v24.8h, v5.8h
add v28.8h, v5.8h, v24.8h
mls v21.8h, v25.8h, v0.h[0]
sqrdmulh v24.8h, v18.8h, v3.h[5]
str q28, [x0, #320]
uzp1 v25.4s, v29.4s, v23.4s
trn1 v28.4s, v16.4s, v26.4s
trn2 v26.4s, v16.4s, v26.4s
mul v16.8h, v18.8h, v3.h[4]
uzp2 v18.4s, v29.4s, v23.4s
str q21, [x0, #304]
sub v29.8h, v26.8h, v28.8h
add v23.8h, v28.8h, v26.8h
sub v21.8h, v18.8h, v25.8h
mul v28.8h, v19.8h, v7.8h
ldr q26, [x2, #944]
ldr q19, [x2, #960]
ldr q6, [x0, #448]
sqrdmulh v17.8h, v29.8h, v17.8h
add v25.8h, v25.8h, v18.8h
ldr q18, [x0, #464]
mul v20.8h, v29.8h, v20.8h
ldr q29, [x2, #976]
mls v16.8h, v24.8h, v0.h[0]
ldr q24, [x2, #992]
sqrdmulh v27.8h, v21.8h, v27.8h
mul v21.8h, v21.8h, v1.8h
mls v20.8h, v17.8h, v0.h[0]
str q16, [x0, #336]
mls v28.8h, v22.8h, v0.h[0]
uzp1 v17.4s, v6.4s, v18.4s
uzp2 v16.4s, v6.4s, v18.4s
ldr q22, [x2, #1008]
ldr q18, [x2, #1024]
ldr q5, [x0, #480]
mls v21.8h, v27.8h, v0.h[0]
ldr q27, [x0, #496]
trn1 v7.2d, v23.2d, v20.2d
trn2 v20.2d, v23.2d, v20.2d
trn1 v23.4s, v31.4s, v28.4s
trn2 v31.4s, v31.4s, v28.4s
ldr q28, [x2, #1040]
sub v1.8h, v20.8h, v7.8h
add v20.8h, v7.8h, v20.8h
trn1 v6.4s, v25.4s, v21.4s
trn2 v25.4s, v25.4s, v21.4s
sqrdmulh v21.8h, v1.8h, v3.h[7]
str q20, [x0, #352]
sub v20.8h, v31.8h, v23.8h
mul v7.8h, v1.8h, v3.h[6]
sub v3.8h, v25.8h, v6.8h
sqrdmulh v1.8h, v20.8h, v2.8h
add v23.8h, v23.8h, v31.8h
mul v31.8h, v20.8h, v30.8h
add v20.8h, v6.8h, v25.8h
ldr q30, [x2, #1056]
sqrdmulh v25.8h, v3.8h, v19.8h
sub v19.8h, v16.8h, v17.8h
mls v7.8h, v21.8h, v0.h[0]
add v21.8h, v17.8h, v16.8h
sqrdmulh v17.8h, v19.8h, v24.8h
uzp1 v16.4s, v5.4s, v27.4s
mls v31.8h, v1.8h, v0.h[0]
uzp2 v24.4s, v5.4s, v27.4s
mul v27.8h, v19.8h, v29.8h
str q7, [x0, #368]
mul v29.8h, v3.8h, v26.8h
sub v19.8h, v24.8h, v16.8h
add v26.8h, v16.8h, v24.8h
ldr q16, [x2, #1072]
ldr q24, [x2, #1088]
ldr q2, [x2, #1104]
trn1 v6.2d, v23.2d, v31.2d
trn2 v23.2d, v23.2d, v31.2d
ldr q1, [x2, #1120]
ldr q5, [x2, #1136]
ldr q7, [x2, #1152]
mls v27.8h, v17.8h, v0.h[0]
ldr q31, [x0, #0]
sub v17.8h, v23.8h, v6.8h
add v23.8h, v6.8h, v23.8h
mls v29.8h, v25.8h, v0.h[0]
ldr q25, [x0, #32]
sqrdmulh v3.8h, v17.8h, v4.h[1]
str q23, [x0, #384]
mul v23.8h, v17.8h, v4.h[0]
trn1 v17.4s, v21.4s, v27.4s
trn2 v27.4s, v21.4s, v27.4s
sqrdmulh v21.8h, v19.8h, v30.8h
trn1 v30.2d, v20.2d, v29.2d
trn2 v20.2d, v20.2d, v29.2d
sub v29.8h, v27.8h, v17.8h
add v17.8h, v17.8h, v27.8h
mls v23.8h, v3.8h, v0.h[0]
sub v27.8h, v20.8h, v30.8h
sqrdmulh v18.8h, v29.8h, v18.8h
add v30.8h, v30.8h, v20.8h
ldr q20, [x0, #64]
mul v22.8h, v29.8h, v22.8h
ldr q29, [x0, #96]
sqrdmulh v6.8h, v27.8h, v4.h[3]
str q30, [x0, #416]
str q23, [x0, #400]
mul v30.8h, v27.8h, v4.h[2]
ldr q23, [x0, #128]
mul v27.8h, v19.8h, v28.8h
ldr q19, [x0, #160]
add v28.8h, v31.8h, v25.8h
mls v22.8h, v18.8h, v0.h[0]
sub v18.8h, v25.8h, v31.8h
ldr q3, [x2, #1168]
mls v30.8h, v6.8h, v0.h[0]
ldr q31, [x0, #192]
add v25.8h, v20.8h, v29.8h
mls v27.8h, v21.8h, v0.h[0]
sub v21.8h, v29.8h, v20.8h
trn1 v20.2d, v17.2d, v22.2d
trn2 v29.2d, v17.2d, v22.2d
ldr q22, [x0, #224]
sub v17.8h, v19.8h, v23.8h
sqrdmulh v6.8h, v18.8h, v5.h[3]
str q30, [x0, #432]
mul v30.8h, v18.8h, v5.h[2]
sub v18.8h, v29.8h, v20.8h
add v20.8h, v20.8h, v29.8h
trn1 v29.4s, v26.4s, v27.4s
trn2 v26.4s, v26.4s, v27.4s
sqrdmulh v27.8h, v18.8h, v4.h[5]
str q20, [x0, #448]
add v20.8h, v23.8h, v19.8h
mul v23.8h, v18.8h, v4.h[4]
sub v19.8h, v26.8h, v29.8h
add v18.8h, v29.8h, v26.8h
add v29.8h, v31.8h, v22.8h
sqrdmulh v26.8h, v19.8h, v24.8h
sub v24.8h, v22.8h, v31.8h
mul v31.8h, v19.8h, v16.8h
ldr q22, [x0, #256]
mls v23.8h, v27.8h, v0.h[0]
ldr q19, [x0, #288]
sqrdmulh v16.8h, v17.8h, v1.h[7]
mul v27.8h, v17.8h, v1.h[6]
mls v31.8h, v26.8h, v0.h[0]
str q23, [x0, #464]
ldr q17, [x0, #320]
sqrdmulh v26.8h, v21.8h, v5.h[1]
mul v23.8h, v21.8h, v5.h[0]
mls v27.8h, v16.8h, v2.h[0]
add v21.8h, v22.8h, v19.8h
trn1 v16.2d, v18.2d, v31.2d
trn2 v18.2d, v18.2d, v31.2d
mls v30.8h, v6.8h, v2.h[0]
sub v31.8h, v19.8h, v22.8h
sub v22.8h, v18.8h, v16.8h
add v19.8h, v16.8h, v18.8h
ldr q16, [x0, #352]
mls v23.8h, v26.8h, v2.h[0]
sqrdmulh v18.8h, v22.8h, v4.h[7]
str q19, [x0, #480]
ldr q26, [x0, #384]
mul v19.8h, v22.8h, v4.h[6]
ldr q22, [x0, #416]
sqrdmulh v6.8h, v24.8h, v1.h[5]
mul v24.8h, v24.8h, v1.h[4]
add v4.8h, v17.8h, v16.8h
sub v17.8h, v16.8h, v17.8h
mls v19.8h, v18.8h, v0.h[0]
ldr q16, [x0, #448]
sqrdmulh v18.8h, v31.8h, v1.h[3]
add v0.8h, v26.8h, v22.8h
sub v26.8h, v22.8h, v26.8h
mul v22.8h, v31.8h, v1.h[2]
str q19, [x0, #496]
sqrdmulh v31.8h, v17.8h, v1.h[1]
mul v19.8h, v17.8h, v1.h[0]
sub v17.8h, v23.8h, v30.8h
mls v24.8h, v6.8h, v2.h[0]
add v30.8h, v30.8h, v23.8h
sqrdmulh v23.8h, v26.8h, v2.h[7]
mul v26.8h, v26.8h, v2.h[6]
mls v22.8h, v18.8h, v2.h[0]
mls v19.8h, v31.8h, v2.h[0]
sub v18.8h, v24.8h, v27.8h
sqrdmulh v31.8h, v17.8h, v3.h[1]
add v27.8h, v27.8h, v24.8h
mls v26.8h, v23.8h, v2.h[0]
ldr q24, [x0, #480]
mul v23.8h, v17.8h, v3.h[0]
sub v17.8h, v19.8h, v22.8h
sqrdmulh v6.8h, v18.8h, v7.h[7]
mul v18.8h, v18.8h, v7.h[6]
add v22.8h, v22.8h, v19.8h
mls v23.8h, v31.8h, v2.h[0]
add v19.8h, v16.8h, v24.8h
sub v31.8h, v24.8h, v16.8h
mls v18.8h, v6.8h, v2.h[0]
ldr q16, [x2, #1184]
sqrdmulh v24.8h, v31.8h, v2.h[5]
mul v31.8h, v31.8h, v2.h[4]
sqrdmulh v6.8h, v17.8h, v7.h[5]
mul v17.8h, v17.8h, v7.h[4]
mls v31.8h, v24.8h, v2.h[0]
sub v24.8h, v20.8h, v16.8h
sub v20.8h, v28.8h, v16.8h
sub v28.8h, v25.8h, v16.8h
sub v25.8h, v29.8h, v16.8h
sqrdmulh v29.8h, v24.8h, v2.h[3]
sub v21.8h, v21.8h, v16.8h
mul v24.8h, v24.8h, v2.h[2]
sub v4.8h, v4.8h, v16.8h
sub v0.8h, v0.8h, v16.8h
sub v16.8h, v19.8h, v16.8h
sqrdmulh v19.8h, v20.8h, v2.h[3]
mul v20.8h, v20.8h, v2.h[2]
mls v24.8h, v29.8h, v2.h[0]
sub v29.8h, v31.8h, v26.8h
mls v17.8h, v6.8h, v2.h[0]
mul v6.8h, v28.8h, v2.h[2]
sqrdmulh v28.8h, v28.8h, v2.h[3]
mls v20.8h, v19.8h, v2.h[0]
sqrdmulh v19.8h, v25.8h, v2.h[3]
add v26.8h, v26.8h, v31.8h
mul v31.8h, v25.8h, v2.h[2]
mls v6.8h, v28.8h, v2.h[0]
sqrdmulh v25.8h, v21.8h, v2.h[3]
sub v28.8h, v27.8h, v30.8h
mul v21.8h, v21.8h, v2.h[2]
add v30.8h, v30.8h, v27.8h
sqrdmulh v27.8h, v4.8h, v2.h[3]
mul v4.8h, v4.8h, v2.h[2]
mls v31.8h, v19.8h, v2.h[0]
sub v19.8h, v6.8h, v20.8h
mls v21.8h, v25.8h, v2.h[0]
add v25.8h, v20.8h, v6.8h
sqrdmulh v20.8h, v0.8h, v2.h[3]
sub v6.8h, v18.8h, v23.8h
mul v0.8h, v0.8h, v2.h[2]
add v23.8h, v23.8h, v18.8h
mls v4.8h, v27.8h, v2.h[0]
sub v18.8h, v31.8h, v24.8h
sqrdmulh v27.8h, v16.8h, v2.h[3]
add v24.8h, v24.8h, v31.8h
mul v31.8h, v16.8h, v2.h[2]
sub v16.8h, v26.8h, v22.8h
mls v0.8h, v20.8h, v2.h[0]
sub v20.8h, v24.8h, v25.8h
add v25.8h, v25.8h, v24.8h
add v24.8h, v22.8h, v26.8h
sub v22.8h, v4.8h, v21.8h
sqrdmulh v26.8h, v19.8h, v3.h[1]
mls v31.8h, v27.8h, v2.h[0]
add v27.8h, v21.8h, v4.8h
mul v21.8h, v19.8h, v3.h[0]
sub v19.8h, v24.8h, v30.8h
sqrdmulh v4.8h, v18.8h, v7.h[7]
add v30.8h, v30.8h, v24.8h
mul v24.8h, v18.8h, v7.h[6]
sub v18.8h, v31.8h, v0.8h
add v31.8h, v0.8h, v31.8h
sqrdmulh v0.8h, v22.8h, v7.h[5]
mul v22.8h, v22.8h, v7.h[4]
mls v21.8h, v26.8h, v2.h[0]
sub v26.8h, v31.8h, v27.8h
mls v24.8h, v4.8h, v2.h[0]
add v27.8h, v27.8h, v31.8h
sqrdmulh v31.8h, v18.8h, v7.h[3]
mul v18.8h, v18.8h, v7.h[2]
sub v4.8h, v27.8h, v25.8h
mls v22.8h, v0.8h, v2.h[0]
add v27.8h, v25.8h, v27.8h
sqrdmulh v25.8h, v29.8h, v7.h[3]
sub v0.8h, v24.8h, v21.8h
mul v29.8h, v29.8h, v7.h[2]
add v24.8h, v21.8h, v24.8h
mls v18.8h, v31.8h, v2.h[0]
sqrdmulh v21.8h, v20.8h, v7.h[1]
mul v31.8h, v20.8h, v7.h[0]
mls v29.8h, v25.8h, v2.h[0]
sub v20.8h, v18.8h, v22.8h
sqrdmulh v25.8h, v28.8h, v7.h[1]
mul v28.8h, v28.8h, v7.h[0]
add v22.8h, v22.8h, v18.8h
sqrdmulh v18.8h, v0.8h, v7.h[1]
mul v0.8h, v0.8h, v7.h[0]
mls v31.8h, v21.8h, v2.h[0]
add v21.8h, v17.8h, v29.8h
sub v17.8h, v29.8h, v17.8h
sqrdmulh v29.8h, v6.8h, v7.h[1]
mul v6.8h, v6.8h, v7.h[0]
mls v28.8h, v25.8h, v2.h[0]
sub v25.8h, v22.8h, v24.8h
mls v0.8h, v18.8h, v2.h[0]
sub v18.8h, v21.8h, v23.8h
add v22.8h, v24.8h, v22.8h
add v24.8h, v23.8h, v21.8h
sqrdmulh v23.8h, v26.8h, v5.h[7]
mul v21.8h, v26.8h, v5.h[6]
sqrdmulh v26.8h, v16.8h, v5.h[7]
mul v16.8h, v16.8h, v5.h[6]
mls v6.8h, v29.8h, v2.h[0]
sqrdmulh v29.8h, v20.8h, v5.h[7]
mul v20.8h, v20.8h, v5.h[6]
mls v21.8h, v23.8h, v2.h[0]
mls v16.8h, v26.8h, v2.h[0]
sqrdmulh v23.8h, v17.8h, v5.h[7]
mls v20.8h, v29.8h, v2.h[0]
mul v26.8h, v17.8h, v5.h[6]
sub v29.8h, v21.8h, v31.8h
sqrdmulh v17.8h, v4.8h, v5.h[5]
add v21.8h, v31.8h, v21.8h
mul v31.8h, v4.8h, v5.h[4]
sub v4.8h, v16.8h, v28.8h
add v16.8h, v28.8h, v16.8h
add v28.8h, v0.8h, v20.8h
mls v26.8h, v23.8h, v2.h[0]
sub v23.8h, v20.8h, v0.8h
sqrdmulh v20.8h, v19.8h, v5.h[5]
mul v19.8h, v19.8h, v5.h[4]
sqrdmulh v0.8h, v25.8h, v5.h[5]
mul v25.8h, v25.8h, v5.h[4]
mls v31.8h, v17.8h, v2.h[0]
sub v17.8h, v26.8h, v6.8h
mls v19.8h, v20.8h, v2.h[0]
add v20.8h, v6.8h, v26.8h
sqrdmulh v26.8h, v18.8h, v5.h[5]
sqrdmulh v6.8h, v27.8h, v2.h[1]
mls v25.8h, v0.8h, v2.h[0]
sshr v0.8h, v31.8h, #15
mul v18.8h, v18.8h, v5.h[4]
sshr v6.8h, v6.8h, #11
mls v27.8h, v6.8h, v2.h[0]
sqrdmulh v6.8h, v30.8h, v2.h[1]
mls v18.8h, v26.8h, v2.h[0]
sqrdmulh v26.8h, v22.8h, v2.h[1]
str q27, [x0, #0]
sshr v27.8h, v6.8h, #11
sqrdmulh v6.8h, v29.8h, v5.h[5]
mul v29.8h, v29.8h, v5.h[4]
sshr v26.8h, v26.8h, #11
mls v30.8h, v27.8h, v2.h[0]
sshr v27.8h, v19.8h, #15
mls v22.8h, v26.8h, v2.h[0]
sshr v26.8h, v18.8h, #15
mls v29.8h, v6.8h, v2.h[0]
sshr v6.8h, v25.8h, #15
str q30, [x0, #32]
sqrdmulh v30.8h, v4.8h, v5.h[5]
mul v4.8h, v4.8h, v5.h[4]
str q22, [x0, #64]
sqrdmulh v22.8h, v23.8h, v5.h[5]
mul v23.8h, v23.8h, v5.h[4]
mls v4.8h, v30.8h, v2.h[0]
sshr v30.8h, v29.8h, #15
mls v23.8h, v22.8h, v2.h[0]
sqrdmulh v22.8h, v24.8h, v2.h[1]
sshr v22.8h, v22.8h, #11
mls v24.8h, v22.8h, v2.h[0]
sqrdmulh v22.8h, v21.8h, v2.h[1]
str q24, [x0, #96]
sqrdmulh v24.8h, v16.8h, v2.h[1]
sshr v22.8h, v22.8h, #11
mls v21.8h, v22.8h, v2.h[0]
sqrdmulh v22.8h, v28.8h, v2.h[1]
sshr v24.8h, v24.8h, #11
mls v16.8h, v24.8h, v2.h[0]
str q21, [x0, #128]
sshr v24.8h, v4.8h, #15
sqrdmulh v21.8h, v17.8h, v5.h[5]
sshr v22.8h, v22.8h, #11
mul v17.8h, v17.8h, v5.h[4]
mls v28.8h, v22.8h, v2.h[0]
str q16, [x0, #160]
sshr v22.8h, v23.8h, #15
sqrdmulh v16.8h, v20.8h, v2.h[1]
mls v17.8h, v21.8h, v2.h[0]
str q28, [x0, #192]
sshr v21.8h, v16.8h, #11
sshr v28.8h, v17.8h, #15
mls v20.8h, v21.8h, v2.h[0]
str q20, [x0, #224]
ldr q16, [x2, #1200]
and v21.16b, v0.16b, v16.16b
and v20.16b, v27.16b, v16.16b
and v27.16b, v6.16b, v16.16b
and v26.16b, v26.16b, v16.16b
add v31.8h, v31.8h, v21.8h
add v21.8h, v19.8h, v20.8h
ldr q20, [x0, #16]
ldr q19, [x0, #48]
add v27.8h, v25.8h, v27.8h
and v25.16b, v30.16b, v16.16b
ldr q30, [x0, #80]
and v24.16b, v24.16b, v16.16b
and v22.16b, v22.16b, v16.16b
str q31, [x0, #256]
str q21, [x0, #288]
ldr q31, [x0, #400]
ldr q21, [x0, #432]
add v18.8h, v18.8h, v26.8h
add v26.8h, v29.8h, v25.8h
ldr q25, [x0, #112]
ldr q29, [x0, #144]
str q27, [x0, #320]
ldr q27, [x0, #464]
add v24.8h, v4.8h, v24.8h
ldr q0, [x0, #176]
and v28.16b, v28.16b, v16.16b
ldr q16, [x0, #496]
add v23.8h, v23.8h, v22.8h
str q18, [x0, #352]
str q26, [x0, #384]
ldr q22, [x0, #208]
ldr q18, [x0, #240]
ldr q26, [x0, #272]
add v28.8h, v17.8h, v28.8h
str q24, [x0, #416]
sub v17.8h, v19.8h, v20.8h
ldr q24, [x0, #304]
str q23, [x0, #448]
add v23.8h, v20.8h, v19.8h
ldr q20, [x0, #336]
ldr q19, [x0, #368]
str q28, [x0, #480]
sqrdmulh v28.8h, v17.8h, v5.h[3]
sub v6.8h, v21.8h, v31.8h
sub v4.8h, v25.8h, v30.8h
add v30.8h, v30.8h, v25.8h
sub v25.8h, v0.8h, v29.8h
add v29.8h, v29.8h, v0.8h
sqrdmulh v0.8h, v23.8h, v2.h[3]
add v31.8h, v31.8h, v21.8h
sub v21.8h, v18.8h, v22.8h
add v22.8h, v22.8h, v18.8h
sub v18.8h, v24.8h, v26.8h
add v26.8h, v26.8h, v24.8h
mul v24.8h, v23.8h, v2.h[2]
sub v23.8h, v19.8h, v20.8h
mul v17.8h, v17.8h, v5.h[2]
add v20.8h, v20.8h, v19.8h
sqrdmulh v19.8h, v4.8h, v5.h[1]
mul v4.8h, v4.8h, v5.h[0]
mls v24.8h, v0.8h, v2.h[0]
sub v0.8h, v16.8h, v27.8h
mls v17.8h, v28.8h, v2.h[0]
add v28.8h, v27.8h, v16.8h
sqrdmulh v27.8h, v30.8h, v2.h[3]
mul v16.8h, v30.8h, v2.h[2]
sqrdmulh v30.8h, v25.8h, v1.h[7]
mul v25.8h, v25.8h, v1.h[6]
mls v4.8h, v19.8h, v2.h[0]
sqrdmulh v19.8h, v29.8h, v2.h[3]
mul v29.8h, v29.8h, v2.h[2]
mls v16.8h, v27.8h, v2.h[0]
sqrdmulh v27.8h, v21.8h, v1.h[5]
mul v21.8h, v21.8h, v1.h[4]
mls v25.8h, v30.8h, v2.h[0]
sub v30.8h, v4.8h, v17.8h
mls v29.8h, v19.8h, v2.h[0]
sub v19.8h, v16.8h, v24.8h
add v24.8h, v24.8h, v16.8h
add v16.8h, v17.8h, v4.8h
sqrdmulh v17.8h, v22.8h, v2.h[3]
mul v22.8h, v22.8h, v2.h[2]
sqrdmulh v4.8h, v18.8h, v1.h[3]
mul v18.8h, v18.8h, v1.h[2]
mls v21.8h, v27.8h, v2.h[0]
mls v22.8h, v17.8h, v2.h[0]
sqrdmulh v27.8h, v26.8h, v2.h[3]
mul v17.8h, v26.8h, v2.h[2]
sqrdmulh v26.8h, v23.8h, v1.h[1]
mul v23.8h, v23.8h, v1.h[0]
sub v1.8h, v22.8h, v29.8h
mls v18.8h, v4.8h, v2.h[0]
add v29.8h, v29.8h, v22.8h
sqrdmulh v22.8h, v20.8h, v2.h[3]
sub v4.8h, v21.8h, v25.8h
mul v20.8h, v20.8h, v2.h[2]
add v25.8h, v25.8h, v21.8h
sqrdmulh v21.8h, v6.8h, v2.h[7]
mul v6.8h, v6.8h, v2.h[6]
mls v17.8h, v27.8h, v2.h[0]
sub v27.8h, v29.8h, v24.8h
mls v23.8h, v26.8h, v2.h[0]
sub v26.8h, v25.8h, v16.8h
mls v20.8h, v22.8h, v2.h[0]
add v22.8h, v24.8h, v29.8h
sqrdmulh v24.8h, v31.8h, v2.h[3]
add v29.8h, v16.8h, v25.8h
mul v16.8h, v31.8h, v2.h[2]
sqrdmulh v25.8h, v0.8h, v2.h[5]
sub v31.8h, v23.8h, v18.8h
mul v0.8h, v0.8h, v2.h[4]
add v18.8h, v18.8h, v23.8h
sqrdmulh v23.8h, v28.8h, v2.h[3]
mul v28.8h, v28.8h, v2.h[2]
mls v6.8h, v21.8h, v2.h[0]
sub v21.8h, v20.8h, v17.8h
mls v16.8h, v24.8h, v2.h[0]
add v24.8h, v17.8h, v20.8h
mls v0.8h, v25.8h, v2.h[0]
ldr q17, [x2, #1200]
mls v28.8h, v23.8h, v2.h[0]
sqrdmulh v20.8h, v19.8h, v3.h[1]
mul v25.8h, v19.8h, v3.h[0]
sqrdmulh v23.8h, v30.8h, v3.h[1]
sub v19.8h, v0.8h, v6.8h
mul v30.8h, v30.8h, v3.h[0]
sub v3.8h, v28.8h, v16.8h
add v28.8h, v16.8h, v28.8h
add v16.8h, v6.8h, v0.8h
mls v25.8h, v20.8h, v2.h[0]
sqrdmulh v20.8h, v1.8h, v7.h[7]
sub v6.8h, v28.8h, v24.8h
mls v30.8h, v23.8h, v2.h[0]
sub v23.8h, v16.8h, v18.8h
mul v0.8h, v1.8h, v7.h[6]
add v24.8h, v24.8h, v28.8h
sqrdmulh v28.8h, v4.8h, v7.h[7]
add v16.8h, v18.8h, v16.8h
mul v18.8h, v4.8h, v7.h[6]
sub v1.8h, v24.8h, v22.8h
sqrdmulh v4.8h, v21.8h, v7.h[5]
add v24.8h, v22.8h, v24.8h
mul v22.8h, v21.8h, v7.h[4]
sub v21.8h, v16.8h, v29.8h
mls v0.8h, v20.8h, v2.h[0]
add v20.8h, v29.8h, v16.8h
sqrdmulh v29.8h, v31.8h, v7.h[5]
mul v16.8h, v31.8h, v7.h[4]
sqrdmulh v31.8h, v3.8h, v7.h[3]
mul v3.8h, v3.8h, v7.h[2]
mls v18.8h, v28.8h, v2.h[0]
sub v28.8h, v0.8h, v25.8h
mls v22.8h, v4.8h, v2.h[0]
add v25.8h, v25.8h, v0.8h
sqrdmulh v4.8h, v19.8h, v7.h[3]
mul v19.8h, v19.8h, v7.h[2]
mls v16.8h, v29.8h, v2.h[0]
sub v29.8h, v18.8h, v30.8h
mls v3.8h, v31.8h, v2.h[0]
add v31.8h, v30.8h, v18.8h
sqrdmulh v30.8h, v27.8h, v7.h[1]
mls v19.8h, v4.8h, v2.h[0]
mul v18.8h, v27.8h, v7.h[0]
sqrdmulh v27.8h, v26.8h, v7.h[1]
sub v0.8h, v3.8h, v22.8h
mul v26.8h, v26.8h, v7.h[0]
add v22.8h, v22.8h, v3.8h
sub v4.8h, v19.8h, v16.8h
mul v3.8h, v23.8h, v5.h[6]
mls v18.8h, v30.8h, v2.h[0]
add v30.8h, v16.8h, v19.8h
sqrdmulh v16.8h, v0.8h, v5.h[7]
sub v19.8h, v22.8h, v25.8h
mls v26.8h, v27.8h, v2.h[0]
sub v27.8h, v30.8h, v31.8h
mul v0.8h, v0.8h, v5.h[6]
add v22.8h, v25.8h, v22.8h
sqrdmulh v25.8h, v4.8h, v5.h[7]
add v30.8h, v31.8h, v30.8h
mul v31.8h, v4.8h, v5.h[6]
sqrdmulh v4.8h, v28.8h, v7.h[1]
mul v28.8h, v28.8h, v7.h[0]
sqrdmulh v23.8h, v23.8h, v5.h[7]
mls v0.8h, v16.8h, v2.h[0]
sqrdmulh v16.8h, v29.8h, v7.h[1]
mul v29.8h, v29.8h, v7.h[0]
sqrdmulh v7.8h, v6.8h, v5.h[7]
mul v6.8h, v6.8h, v5.h[6]
mls v3.8h, v23.8h, v2.h[0]
mls v31.8h, v25.8h, v2.h[0]
mls v28.8h, v4.8h, v2.h[0]
mls v29.8h, v16.8h, v2.h[0]
mls v6.8h, v7.8h, v2.h[0]
sub v23.8h, v3.8h, v26.8h
sqrdmulh v25.8h, v1.8h, v5.h[5]
add v16.8h, v26.8h, v3.8h
mul v26.8h, v1.8h, v5.h[4]
sub v4.8h, v0.8h, v28.8h
sqrdmulh v7.8h, v24.8h, v2.h[1]
sub v3.8h, v31.8h, v29.8h
sub v1.8h, v6.8h, v18.8h
add v18.8h, v18.8h, v6.8h
sqrdmulh v6.8h, v21.8h, v5.h[5]
add v28.8h, v28.8h, v0.8h
mls v26.8h, v25.8h, v2.h[0]
add v25.8h, v29.8h, v31.8h
sshr v31.8h, v7.8h, #11
mul v29.8h, v21.8h, v5.h[4]
sqrdmulh v21.8h, v19.8h, v5.h[5]
mls v24.8h, v31.8h, v2.h[0]
sshr v31.8h, v26.8h, #15
mul v19.8h, v19.8h, v5.h[4]
sqrdmulh v0.8h, v27.8h, v5.h[5]
and v31.16b, v31.16b, v17.16b
mul v27.8h, v27.8h, v5.h[4]
sqrdmulh v7.8h, v1.8h, v5.h[5]
str q24, [x0, #16]
add v24.8h, v26.8h, v31.8h
mul v26.8h, v1.8h, v5.h[4]
mls v29.8h, v6.8h, v2.h[0]
sqrdmulh v31.8h, v20.8h, v2.h[1]
str q24, [x0, #272]
mls v19.8h, v21.8h, v2.h[0]
sqrdmulh v24.8h, v22.8h, v2.h[1]
mls v27.8h, v0.8h, v2.h[0]
sshr v21.8h, v29.8h, #15
sqrdmulh v1.8h, v30.8h, v2.h[1]
sshr v31.8h, v31.8h, #11
mls v26.8h, v7.8h, v2.h[0]
sshr v6.8h, v19.8h, #15
sqrdmulh v0.8h, v18.8h, v2.h[1]
sshr v24.8h, v24.8h, #11
sshr v7.8h, v27.8h, #15
mls v20.8h, v31.8h, v2.h[0]
sshr v31.8h, v1.8h, #11
and v21.16b, v21.16b, v17.16b
mls v22.8h, v24.8h, v2.h[0]
and v24.16b, v6.16b, v17.16b
sshr v1.8h, v0.8h, #11
mls v30.8h, v31.8h, v2.h[0]
and v31.16b, v7.16b, v17.16b
add v21.8h, v29.8h, v21.8h
str q20, [x0, #48]
add v29.8h, v19.8h, v24.8h
sqrdmulh v20.8h, v23.8h, v5.h[5]
add v24.8h, v27.8h, v31.8h
mul v19.8h, v23.8h, v5.h[4]
str q22, [x0, #80]
str q21, [x0, #304]
sqrdmulh v27.8h, v4.8h, v5.h[5]
sshr v31.8h, v26.8h, #15
str q30, [x0, #112]
str q29, [x0, #336]
mul v23.8h, v4.8h, v5.h[4]
str q24, [x0, #368]
sqrdmulh v22.8h, v3.8h, v5.h[5]
and v21.16b, v31.16b, v17.16b
mul v30.8h, v3.8h, v5.h[4]
mls v19.8h, v20.8h, v2.h[0]
add v29.8h, v26.8h, v21.8h
sqrdmulh v24.8h, v16.8h, v2.h[1]
mls v23.8h, v27.8h, v2.h[0]
str q29, [x0, #400]
sqrdmulh v31.8h, v28.8h, v2.h[1]
mls v30.8h, v22.8h, v2.h[0]
sshr v20.8h, v19.8h, #15
sqrdmulh v21.8h, v25.8h, v2.h[1]
sshr v26.8h, v24.8h, #11
sshr v27.8h, v23.8h, #15
mls v18.8h, v1.8h, v2.h[0]
sshr v29.8h, v31.8h, #11
mls v16.8h, v26.8h, v2.h[0]
sshr v22.8h, v30.8h, #15
and v24.16b, v20.16b, v17.16b
sshr v31.8h, v21.8h, #11
mls v28.8h, v29.8h, v2.h[0]
and v26.16b, v27.16b, v17.16b
and v20.16b, v22.16b, v17.16b
str q18, [x0, #144]
mls v25.8h, v31.8h, v2.h[0]
add v21.8h, v19.8h, v24.8h
str q16, [x0, #176]
add v29.8h, v23.8h, v26.8h
add v27.8h, v30.8h, v20.8h
str q28, [x0, #208]
str q21, [x0, #432]
str q29, [x0, #464]
str q27, [x0, #496]
str q25, [x0, #240]
ret
.section .rodata
.p2align 4
cr_inv_ls_t:
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

