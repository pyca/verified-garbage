// The functions of `src/internal/vg_ed448_verify_equation.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_verify_equation:
	mflr %r7
	std %r7, 3536(%r6)
	std %r14, 3544(%r6)
	lbz %r7, 0(%r3)
	stb %r7, 3288(%r6)
	lbz %r7, 1(%r3)
	stb %r7, 3289(%r6)
	lbz %r7, 2(%r3)
	stb %r7, 3290(%r6)
	lbz %r7, 3(%r3)
	stb %r7, 3291(%r6)
	lbz %r7, 4(%r3)
	stb %r7, 3292(%r6)
	lbz %r7, 5(%r3)
	stb %r7, 3293(%r6)
	lbz %r7, 6(%r3)
	stb %r7, 3294(%r6)
	lbz %r7, 7(%r3)
	stb %r7, 3295(%r6)
	lbz %r7, 8(%r3)
	stb %r7, 3296(%r6)
	lbz %r7, 9(%r3)
	stb %r7, 3297(%r6)
	lbz %r7, 10(%r3)
	stb %r7, 3298(%r6)
	lbz %r7, 11(%r3)
	stb %r7, 3299(%r6)
	lbz %r7, 12(%r3)
	stb %r7, 3300(%r6)
	lbz %r7, 13(%r3)
	stb %r7, 3301(%r6)
	lbz %r7, 14(%r3)
	stb %r7, 3302(%r6)
	lbz %r7, 15(%r3)
	stb %r7, 3303(%r6)
	lbz %r7, 16(%r3)
	stb %r7, 3304(%r6)
	lbz %r7, 17(%r3)
	stb %r7, 3305(%r6)
	lbz %r7, 18(%r3)
	stb %r7, 3306(%r6)
	lbz %r7, 19(%r3)
	stb %r7, 3307(%r6)
	lbz %r7, 20(%r3)
	stb %r7, 3308(%r6)
	lbz %r7, 21(%r3)
	stb %r7, 3309(%r6)
	lbz %r7, 22(%r3)
	stb %r7, 3310(%r6)
	lbz %r7, 23(%r3)
	stb %r7, 3311(%r6)
	lbz %r7, 24(%r3)
	stb %r7, 3312(%r6)
	lbz %r7, 25(%r3)
	stb %r7, 3313(%r6)
	lbz %r7, 26(%r3)
	stb %r7, 3314(%r6)
	lbz %r7, 27(%r3)
	stb %r7, 3315(%r6)
	lbz %r7, 28(%r3)
	stb %r7, 3316(%r6)
	lbz %r7, 29(%r3)
	stb %r7, 3317(%r6)
	lbz %r7, 30(%r3)
	stb %r7, 3318(%r6)
	lbz %r7, 31(%r3)
	stb %r7, 3319(%r6)
	lbz %r7, 32(%r3)
	stb %r7, 3320(%r6)
	lbz %r7, 33(%r3)
	stb %r7, 3321(%r6)
	lbz %r7, 34(%r3)
	stb %r7, 3322(%r6)
	lbz %r7, 35(%r3)
	stb %r7, 3323(%r6)
	lbz %r7, 36(%r3)
	stb %r7, 3324(%r6)
	lbz %r7, 37(%r3)
	stb %r7, 3325(%r6)
	lbz %r7, 38(%r3)
	stb %r7, 3326(%r6)
	lbz %r7, 39(%r3)
	stb %r7, 3327(%r6)
	lbz %r7, 40(%r3)
	stb %r7, 3328(%r6)
	lbz %r7, 41(%r3)
	stb %r7, 3329(%r6)
	lbz %r7, 42(%r3)
	stb %r7, 3330(%r6)
	lbz %r7, 43(%r3)
	stb %r7, 3331(%r6)
	lbz %r7, 44(%r3)
	stb %r7, 3332(%r6)
	lbz %r7, 45(%r3)
	stb %r7, 3333(%r6)
	lbz %r7, 46(%r3)
	stb %r7, 3334(%r6)
	lbz %r7, 47(%r3)
	stb %r7, 3335(%r6)
	lbz %r7, 48(%r3)
	stb %r7, 3336(%r6)
	lbz %r7, 49(%r3)
	stb %r7, 3337(%r6)
	lbz %r7, 50(%r3)
	stb %r7, 3338(%r6)
	lbz %r7, 51(%r3)
	stb %r7, 3339(%r6)
	lbz %r7, 52(%r3)
	stb %r7, 3340(%r6)
	lbz %r7, 53(%r3)
	stb %r7, 3341(%r6)
	lbz %r7, 54(%r3)
	stb %r7, 3342(%r6)
	lbz %r7, 55(%r3)
	stb %r7, 3343(%r6)
	lbz %r7, 56(%r3)
	stb %r7, 3344(%r6)
	lbz %r7, 0(%r4)
	stb %r7, 3345(%r6)
	lbz %r7, 1(%r4)
	stb %r7, 3346(%r6)
	lbz %r7, 2(%r4)
	stb %r7, 3347(%r6)
	lbz %r7, 3(%r4)
	stb %r7, 3348(%r6)
	lbz %r7, 4(%r4)
	stb %r7, 3349(%r6)
	lbz %r7, 5(%r4)
	stb %r7, 3350(%r6)
	lbz %r7, 6(%r4)
	stb %r7, 3351(%r6)
	lbz %r7, 7(%r4)
	stb %r7, 3352(%r6)
	lbz %r7, 8(%r4)
	stb %r7, 3353(%r6)
	lbz %r7, 9(%r4)
	stb %r7, 3354(%r6)
	lbz %r7, 10(%r4)
	stb %r7, 3355(%r6)
	lbz %r7, 11(%r4)
	stb %r7, 3356(%r6)
	lbz %r7, 12(%r4)
	stb %r7, 3357(%r6)
	lbz %r7, 13(%r4)
	stb %r7, 3358(%r6)
	lbz %r7, 14(%r4)
	stb %r7, 3359(%r6)
	lbz %r7, 15(%r4)
	stb %r7, 3360(%r6)
	lbz %r7, 16(%r4)
	stb %r7, 3361(%r6)
	lbz %r7, 17(%r4)
	stb %r7, 3362(%r6)
	lbz %r7, 18(%r4)
	stb %r7, 3363(%r6)
	lbz %r7, 19(%r4)
	stb %r7, 3364(%r6)
	lbz %r7, 20(%r4)
	stb %r7, 3365(%r6)
	lbz %r7, 21(%r4)
	stb %r7, 3366(%r6)
	lbz %r7, 22(%r4)
	stb %r7, 3367(%r6)
	lbz %r7, 23(%r4)
	stb %r7, 3368(%r6)
	lbz %r7, 24(%r4)
	stb %r7, 3369(%r6)
	lbz %r7, 25(%r4)
	stb %r7, 3370(%r6)
	lbz %r7, 26(%r4)
	stb %r7, 3371(%r6)
	lbz %r7, 27(%r4)
	stb %r7, 3372(%r6)
	lbz %r7, 28(%r4)
	stb %r7, 3373(%r6)
	lbz %r7, 29(%r4)
	stb %r7, 3374(%r6)
	lbz %r7, 30(%r4)
	stb %r7, 3375(%r6)
	lbz %r7, 31(%r4)
	stb %r7, 3376(%r6)
	lbz %r7, 32(%r4)
	stb %r7, 3377(%r6)
	lbz %r7, 33(%r4)
	stb %r7, 3378(%r6)
	lbz %r7, 34(%r4)
	stb %r7, 3379(%r6)
	lbz %r7, 35(%r4)
	stb %r7, 3380(%r6)
	lbz %r7, 36(%r4)
	stb %r7, 3381(%r6)
	lbz %r7, 37(%r4)
	stb %r7, 3382(%r6)
	lbz %r7, 38(%r4)
	stb %r7, 3383(%r6)
	lbz %r7, 39(%r4)
	stb %r7, 3384(%r6)
	lbz %r7, 40(%r4)
	stb %r7, 3385(%r6)
	lbz %r7, 41(%r4)
	stb %r7, 3386(%r6)
	lbz %r7, 42(%r4)
	stb %r7, 3387(%r6)
	lbz %r7, 43(%r4)
	stb %r7, 3388(%r6)
	lbz %r7, 44(%r4)
	stb %r7, 3389(%r6)
	lbz %r7, 45(%r4)
	stb %r7, 3390(%r6)
	lbz %r7, 46(%r4)
	stb %r7, 3391(%r6)
	lbz %r7, 47(%r4)
	stb %r7, 3392(%r6)
	lbz %r7, 48(%r4)
	stb %r7, 3393(%r6)
	lbz %r7, 49(%r4)
	stb %r7, 3394(%r6)
	lbz %r7, 50(%r4)
	stb %r7, 3395(%r6)
	lbz %r7, 51(%r4)
	stb %r7, 3396(%r6)
	lbz %r7, 52(%r4)
	stb %r7, 3397(%r6)
	lbz %r7, 53(%r4)
	stb %r7, 3398(%r6)
	lbz %r7, 54(%r4)
	stb %r7, 3399(%r6)
	lbz %r7, 55(%r4)
	stb %r7, 3400(%r6)
	lbz %r7, 56(%r4)
	stb %r7, 3401(%r6)
	lbz %r7, 57(%r4)
	stb %r7, 3402(%r6)
	lbz %r7, 58(%r4)
	stb %r7, 3403(%r6)
	lbz %r7, 59(%r4)
	stb %r7, 3404(%r6)
	lbz %r7, 60(%r4)
	stb %r7, 3405(%r6)
	lbz %r7, 61(%r4)
	stb %r7, 3406(%r6)
	lbz %r7, 62(%r4)
	stb %r7, 3407(%r6)
	lbz %r7, 63(%r4)
	stb %r7, 3408(%r6)
	lbz %r7, 64(%r4)
	stb %r7, 3409(%r6)
	lbz %r7, 65(%r4)
	stb %r7, 3410(%r6)
	lbz %r7, 66(%r4)
	stb %r7, 3411(%r6)
	lbz %r7, 67(%r4)
	stb %r7, 3412(%r6)
	lbz %r7, 68(%r4)
	stb %r7, 3413(%r6)
	lbz %r7, 69(%r4)
	stb %r7, 3414(%r6)
	lbz %r7, 70(%r4)
	stb %r7, 3415(%r6)
	lbz %r7, 71(%r4)
	stb %r7, 3416(%r6)
	lbz %r7, 72(%r4)
	stb %r7, 3417(%r6)
	lbz %r7, 73(%r4)
	stb %r7, 3418(%r6)
	lbz %r7, 74(%r4)
	stb %r7, 3419(%r6)
	lbz %r7, 75(%r4)
	stb %r7, 3420(%r6)
	lbz %r7, 76(%r4)
	stb %r7, 3421(%r6)
	lbz %r7, 77(%r4)
	stb %r7, 3422(%r6)
	lbz %r7, 78(%r4)
	stb %r7, 3423(%r6)
	lbz %r7, 79(%r4)
	stb %r7, 3424(%r6)
	lbz %r7, 80(%r4)
	stb %r7, 3425(%r6)
	lbz %r7, 81(%r4)
	stb %r7, 3426(%r6)
	lbz %r7, 82(%r4)
	stb %r7, 3427(%r6)
	lbz %r7, 83(%r4)
	stb %r7, 3428(%r6)
	lbz %r7, 84(%r4)
	stb %r7, 3429(%r6)
	lbz %r7, 85(%r4)
	stb %r7, 3430(%r6)
	lbz %r7, 86(%r4)
	stb %r7, 3431(%r6)
	lbz %r7, 87(%r4)
	stb %r7, 3432(%r6)
	lbz %r7, 88(%r4)
	stb %r7, 3433(%r6)
	lbz %r7, 89(%r4)
	stb %r7, 3434(%r6)
	lbz %r7, 90(%r4)
	stb %r7, 3435(%r6)
	lbz %r7, 91(%r4)
	stb %r7, 3436(%r6)
	lbz %r7, 92(%r4)
	stb %r7, 3437(%r6)
	lbz %r7, 93(%r4)
	stb %r7, 3438(%r6)
	lbz %r7, 94(%r4)
	stb %r7, 3439(%r6)
	lbz %r7, 95(%r4)
	stb %r7, 3440(%r6)
	lbz %r7, 96(%r4)
	stb %r7, 3441(%r6)
	lbz %r7, 97(%r4)
	stb %r7, 3442(%r6)
	lbz %r7, 98(%r4)
	stb %r7, 3443(%r6)
	lbz %r7, 99(%r4)
	stb %r7, 3444(%r6)
	lbz %r7, 100(%r4)
	stb %r7, 3445(%r6)
	lbz %r7, 101(%r4)
	stb %r7, 3446(%r6)
	lbz %r7, 102(%r4)
	stb %r7, 3447(%r6)
	lbz %r7, 103(%r4)
	stb %r7, 3448(%r6)
	lbz %r7, 104(%r4)
	stb %r7, 3449(%r6)
	lbz %r7, 105(%r4)
	stb %r7, 3450(%r6)
	lbz %r7, 106(%r4)
	stb %r7, 3451(%r6)
	lbz %r7, 107(%r4)
	stb %r7, 3452(%r6)
	lbz %r7, 108(%r4)
	stb %r7, 3453(%r6)
	lbz %r7, 109(%r4)
	stb %r7, 3454(%r6)
	lbz %r7, 110(%r4)
	stb %r7, 3455(%r6)
	lbz %r7, 111(%r4)
	stb %r7, 3456(%r6)
	lbz %r7, 112(%r4)
	stb %r7, 3457(%r6)
	lbz %r7, 113(%r4)
	stb %r7, 3458(%r6)
	lbz %r7, 0(%r5)
	stb %r7, 3459(%r6)
	lbz %r7, 1(%r5)
	stb %r7, 3460(%r6)
	lbz %r7, 2(%r5)
	stb %r7, 3461(%r6)
	lbz %r7, 3(%r5)
	stb %r7, 3462(%r6)
	lbz %r7, 4(%r5)
	stb %r7, 3463(%r6)
	lbz %r7, 5(%r5)
	stb %r7, 3464(%r6)
	lbz %r7, 6(%r5)
	stb %r7, 3465(%r6)
	lbz %r7, 7(%r5)
	stb %r7, 3466(%r6)
	lbz %r7, 8(%r5)
	stb %r7, 3467(%r6)
	lbz %r7, 9(%r5)
	stb %r7, 3468(%r6)
	lbz %r7, 10(%r5)
	stb %r7, 3469(%r6)
	lbz %r7, 11(%r5)
	stb %r7, 3470(%r6)
	lbz %r7, 12(%r5)
	stb %r7, 3471(%r6)
	lbz %r7, 13(%r5)
	stb %r7, 3472(%r6)
	lbz %r7, 14(%r5)
	stb %r7, 3473(%r6)
	lbz %r7, 15(%r5)
	stb %r7, 3474(%r6)
	lbz %r7, 16(%r5)
	stb %r7, 3475(%r6)
	lbz %r7, 17(%r5)
	stb %r7, 3476(%r6)
	lbz %r7, 18(%r5)
	stb %r7, 3477(%r6)
	lbz %r7, 19(%r5)
	stb %r7, 3478(%r6)
	lbz %r7, 20(%r5)
	stb %r7, 3479(%r6)
	lbz %r7, 21(%r5)
	stb %r7, 3480(%r6)
	lbz %r7, 22(%r5)
	stb %r7, 3481(%r6)
	lbz %r7, 23(%r5)
	stb %r7, 3482(%r6)
	lbz %r7, 24(%r5)
	stb %r7, 3483(%r6)
	lbz %r7, 25(%r5)
	stb %r7, 3484(%r6)
	lbz %r7, 26(%r5)
	stb %r7, 3485(%r6)
	lbz %r7, 27(%r5)
	stb %r7, 3486(%r6)
	lbz %r7, 28(%r5)
	stb %r7, 3487(%r6)
	lbz %r7, 29(%r5)
	stb %r7, 3488(%r6)
	lbz %r7, 30(%r5)
	stb %r7, 3489(%r6)
	lbz %r7, 31(%r5)
	stb %r7, 3490(%r6)
	lbz %r7, 32(%r5)
	stb %r7, 3491(%r6)
	lbz %r7, 33(%r5)
	stb %r7, 3492(%r6)
	lbz %r7, 34(%r5)
	stb %r7, 3493(%r6)
	lbz %r7, 35(%r5)
	stb %r7, 3494(%r6)
	lbz %r7, 36(%r5)
	stb %r7, 3495(%r6)
	lbz %r7, 37(%r5)
	stb %r7, 3496(%r6)
	lbz %r7, 38(%r5)
	stb %r7, 3497(%r6)
	lbz %r7, 39(%r5)
	stb %r7, 3498(%r6)
	lbz %r7, 40(%r5)
	stb %r7, 3499(%r6)
	lbz %r7, 41(%r5)
	stb %r7, 3500(%r6)
	lbz %r7, 42(%r5)
	stb %r7, 3501(%r6)
	lbz %r7, 43(%r5)
	stb %r7, 3502(%r6)
	lbz %r7, 44(%r5)
	stb %r7, 3503(%r6)
	lbz %r7, 45(%r5)
	stb %r7, 3504(%r6)
	lbz %r7, 46(%r5)
	stb %r7, 3505(%r6)
	lbz %r7, 47(%r5)
	stb %r7, 3506(%r6)
	lbz %r7, 48(%r5)
	stb %r7, 3507(%r6)
	lbz %r7, 49(%r5)
	stb %r7, 3508(%r6)
	lbz %r7, 50(%r5)
	stb %r7, 3509(%r6)
	lbz %r7, 51(%r5)
	stb %r7, 3510(%r6)
	lbz %r7, 52(%r5)
	stb %r7, 3511(%r6)
	lbz %r7, 53(%r5)
	stb %r7, 3512(%r6)
	lbz %r7, 54(%r5)
	stb %r7, 3513(%r6)
	lbz %r7, 55(%r5)
	stb %r7, 3514(%r6)
	lbz %r7, 56(%r5)
	stb %r7, 3515(%r6)
	addi %r3, %r6, 4096
	li %r7, 0
	std %r7, 3520(%r6)
	lis %r7, -1
	ori %r7, %r7, 26454
	stw %r7, 336(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 340(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 344(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 348(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 352(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 356(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 360(%r6)
	lis %r7, -1
	ori %r7, %r7, 65534
	stw %r7, 364(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 368(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 372(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 376(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 380(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 384(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 388(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 3232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3252(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3256(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3260(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3264(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3268(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3272(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3276(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3280(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3284(%r6)
	lwz %r7, 3345(%r6)
	stw %r7, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r7, 3349(%r6)
	stw %r7, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r7, 3353(%r6)
	stw %r7, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 3357(%r6)
	stw %r7, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 3361(%r6)
	stw %r7, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 3365(%r6)
	stw %r7, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 3369(%r6)
	stw %r7, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 3373(%r6)
	stw %r7, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 3377(%r6)
	stw %r7, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 3381(%r6)
	stw %r7, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 3385(%r6)
	stw %r7, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 3389(%r6)
	stw %r7, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 3393(%r6)
	stw %r7, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 3397(%r6)
	stw %r7, 220(%r6)
	stw %r7, 108(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	lwz %r8, 3345(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	lwz %r8, 3349(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	lwz %r8, 3353(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	lwz %r8, 3357(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	lwz %r8, 3361(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	lwz %r8, 3365(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	lwz %r8, 3369(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	lwz %r8, 3373(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	lwz %r8, 3377(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	lwz %r8, 3381(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	lwz %r8, 3385(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	lwz %r8, 3389(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	lwz %r8, 3393(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	lwz %r8, 3397(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r10
	std %r9, 3520(%r6)
	lbz %r7, 3401(%r6)
	li %r8, 127
	and %r8, %r7, %r8
	ld %r9, 3520(%r6)
	or %r9, %r9, %r8
	std %r9, 3520(%r6)
	rldicl %r7, %r7, 57, 7
	stb %r7, 3528(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 256(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 260(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 264(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 268(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 272(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 276(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
20:
	ld %r4, 168(%r9)
	li %r8, 0
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 20b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 284(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 280(%r6)
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 284(%r6)
	add %r7, %r7, %r8
	stw %r7, 284(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 288(%r6)
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 280(%r6)
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 284(%r6)
	add %r7, %r7, %r8
	stw %r7, 284(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 288(%r6)
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	ld %r7, 280(%r6)
	ld %r8, 224(%r6)
	subfc %r7, %r8, %r7
	std %r7, 392(%r6)
	ld %r7, 288(%r6)
	ld %r8, 232(%r6)
	subfe %r7, %r8, %r7
	std %r7, 400(%r6)
	ld %r7, 296(%r6)
	ld %r8, 240(%r6)
	subfe %r7, %r8, %r7
	std %r7, 408(%r6)
	ld %r7, 304(%r6)
	ld %r8, 248(%r6)
	subfe %r7, %r8, %r7
	std %r7, 416(%r6)
	ld %r7, 312(%r6)
	ld %r8, 256(%r6)
	subfe %r7, %r8, %r7
	std %r7, 424(%r6)
	ld %r7, 320(%r6)
	ld %r8, 264(%r6)
	subfe %r7, %r8, %r7
	std %r7, 432(%r6)
	ld %r7, 328(%r6)
	ld %r8, 272(%r6)
	subfe %r7, %r8, %r7
	std %r7, 440(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 392(%r6)
	subfc %r7, %r4, %r7
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	subfe %r7, %r8, %r7
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	subfe %r7, %r8, %r7
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	subfe %r7, %r5, %r7
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	subfe %r7, %r8, %r7
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	subfe %r7, %r8, %r7
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	subfe %r7, %r8, %r7
	std %r7, 440(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 392(%r6)
	subfc %r7, %r4, %r7
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	subfe %r7, %r8, %r7
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	subfe %r7, %r8, %r7
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	subfe %r7, %r5, %r7
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	subfe %r7, %r8, %r7
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	subfe %r7, %r8, %r7
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	subfe %r7, %r8, %r7
	std %r7, 440(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
21:
	ld %r4, 336(%r9)
	li %r8, 0
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 320(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 328(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 21b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	ld %r7, 448(%r6)
	ld %r8, 224(%r6)
	subfc %r7, %r8, %r7
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	ld %r8, 232(%r6)
	subfe %r7, %r8, %r7
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	ld %r8, 240(%r6)
	subfe %r7, %r8, %r7
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	ld %r8, 248(%r6)
	subfe %r7, %r8, %r7
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	ld %r8, 256(%r6)
	subfe %r7, %r8, %r7
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	ld %r8, 264(%r6)
	subfe %r7, %r8, %r7
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	ld %r8, 272(%r6)
	subfe %r7, %r8, %r7
	std %r7, 496(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 448(%r6)
	subfc %r7, %r4, %r7
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	subfe %r7, %r8, %r7
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	subfe %r7, %r8, %r7
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	subfe %r7, %r5, %r7
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	subfe %r7, %r8, %r7
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	subfe %r7, %r8, %r7
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	subfe %r7, %r8, %r7
	std %r7, 496(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 448(%r6)
	subfc %r7, %r4, %r7
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	subfe %r7, %r8, %r7
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	subfe %r7, %r8, %r7
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	subfe %r7, %r5, %r7
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	subfe %r7, %r8, %r7
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	subfe %r7, %r8, %r7
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	subfe %r7, %r8, %r7
	std %r7, 496(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
22:
	ld %r4, 392(%r9)
	li %r8, 0
	ld %r5, 392(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 400(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 408(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 416(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 424(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 432(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 440(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
23:
	ld %r4, 504(%r9)
	li %r8, 0
	ld %r5, 392(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 400(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 408(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 416(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 424(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 432(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 440(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
24:
	ld %r4, 504(%r9)
	li %r8, 0
	ld %r5, 448(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 456(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 464(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 472(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
25:
	ld %r4, 392(%r9)
	li %r8, 0
	ld %r5, 448(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 456(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 464(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 472(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
26:
	ld %r4, 560(%r9)
	li %r8, 0
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 26b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
27:
	ld %r4, 504(%r9)
	li %r8, 0
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 27b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 112(%r6)
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 112(%r6)
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 1
	li %r5, 0
	stw %r4, 840(%r6)
	stw %r5, 844(%r6)
	stw %r5, 848(%r6)
	stw %r5, 852(%r6)
	stw %r5, 856(%r6)
	stw %r5, 860(%r6)
	stw %r5, 864(%r6)
	stw %r5, 868(%r6)
	stw %r5, 872(%r6)
	stw %r5, 876(%r6)
	stw %r5, 880(%r6)
	stw %r5, 884(%r6)
	stw %r5, 888(%r6)
	stw %r5, 892(%r6)
	li %r12, 446
28:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
29:
	ld %r4, 840(%r9)
	li %r8, 0
	ld %r5, 840(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 848(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 856(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 864(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 872(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 880(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 888(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 29b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r5, %r12, -222
	cmpldi %cr0, %r5, 0
	beq %cr0, 210f
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
212:
	ld %r4, 840(%r9)
	li %r8, 0
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 212b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	b 211f
210:
211:
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
213:
	ld %r4, 504(%r9)
	li %r8, 0
	ld %r5, 840(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 848(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 856(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 864(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 872(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 880(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 888(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 213b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 672(%r6)
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 672(%r6)
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
214:
	ld %r4, 672(%r9)
	li %r8, 0
	ld %r5, 672(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 680(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 688(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 696(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 704(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 712(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 720(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 214b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
215:
	ld %r4, 448(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 215b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	ld %r7, 616(%r6)
	ld %r8, 392(%r6)
	subfc %r7, %r8, %r7
	std %r7, 56(%r6)
	ld %r7, 624(%r6)
	ld %r8, 400(%r6)
	subfe %r7, %r8, %r7
	std %r7, 64(%r6)
	ld %r7, 632(%r6)
	ld %r8, 408(%r6)
	subfe %r7, %r8, %r7
	std %r7, 72(%r6)
	ld %r7, 640(%r6)
	ld %r8, 416(%r6)
	subfe %r7, %r8, %r7
	std %r7, 80(%r6)
	ld %r7, 648(%r6)
	ld %r8, 424(%r6)
	subfe %r7, %r8, %r7
	std %r7, 88(%r6)
	ld %r7, 656(%r6)
	ld %r8, 432(%r6)
	subfe %r7, %r8, %r7
	std %r7, 96(%r6)
	ld %r7, 664(%r6)
	ld %r8, 440(%r6)
	subfe %r7, %r8, %r7
	std %r7, 104(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 56(%r6)
	subfc %r7, %r4, %r7
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	subfe %r7, %r8, %r7
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	subfe %r7, %r8, %r7
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	subfe %r7, %r5, %r7
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	subfe %r7, %r8, %r7
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	subfe %r7, %r8, %r7
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	subfe %r7, %r8, %r7
	std %r7, 104(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 56(%r6)
	subfc %r7, %r4, %r7
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	subfe %r7, %r8, %r7
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	subfe %r7, %r8, %r7
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	subfe %r7, %r5, %r7
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	subfe %r7, %r8, %r7
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	subfe %r7, %r8, %r7
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	subfe %r7, %r8, %r7
	std %r7, 104(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	or %r10, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r10
	std %r9, 3520(%r6)
	li %r11, 0
	lwz %r5, 672(%r6)
	lwz %r7, 672(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 56(%r6)
	lwz %r5, 676(%r6)
	lwz %r7, 676(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 60(%r6)
	lwz %r5, 680(%r6)
	lwz %r7, 680(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 64(%r6)
	lwz %r5, 684(%r6)
	lwz %r7, 684(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 68(%r6)
	lwz %r5, 688(%r6)
	lwz %r7, 688(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 72(%r6)
	lwz %r5, 692(%r6)
	lwz %r7, 692(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 76(%r6)
	lwz %r5, 696(%r6)
	lwz %r7, 696(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 80(%r6)
	lwz %r5, 700(%r6)
	lwz %r7, 700(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 84(%r6)
	lwz %r5, 704(%r6)
	lwz %r7, 704(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 88(%r6)
	lwz %r5, 708(%r6)
	lwz %r7, 708(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 92(%r6)
	lwz %r5, 712(%r6)
	lwz %r7, 712(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 96(%r6)
	lwz %r5, 716(%r6)
	lwz %r7, 716(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 100(%r6)
	lwz %r5, 720(%r6)
	lwz %r7, 720(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 104(%r6)
	lwz %r5, 724(%r6)
	lwz %r7, 724(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 108(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	or %r10, %r10, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	lbz %r7, 3528(%r6)
	and %r8, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r8
	std %r9, 3520(%r6)
	ld %r7, 672(%r6)
	ld %r8, 672(%r6)
	subfc %r7, %r8, %r7
	std %r7, 616(%r6)
	ld %r7, 680(%r6)
	ld %r8, 680(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 688(%r6)
	ld %r8, 688(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 696(%r6)
	ld %r8, 696(%r6)
	subfe %r7, %r8, %r7
	std %r7, 640(%r6)
	ld %r7, 704(%r6)
	ld %r8, 704(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 712(%r6)
	ld %r8, 712(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 720(%r6)
	ld %r8, 720(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 616(%r6)
	subfc %r7, %r4, %r7
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	subfe %r7, %r5, %r7
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 616(%r6)
	subfc %r7, %r4, %r7
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	subfe %r7, %r5, %r7
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	ld %r7, 616(%r6)
	ld %r8, 672(%r6)
	subfc %r7, %r8, %r7
	std %r7, 728(%r6)
	ld %r7, 624(%r6)
	ld %r8, 680(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 632(%r6)
	ld %r8, 688(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 640(%r6)
	ld %r8, 696(%r6)
	subfe %r7, %r8, %r7
	std %r7, 752(%r6)
	ld %r7, 648(%r6)
	ld %r8, 704(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 656(%r6)
	ld %r8, 712(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 664(%r6)
	ld %r8, 720(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	lbz %r8, 0(%r3)
	li %r9, 1
	and %r8, %r8, %r9
	lbz %r7, 3528(%r6)
	xor %r8, %r8, %r7
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 728(%r6)
	lwz %r7, 672(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3120(%r6)
	lwz %r5, 732(%r6)
	lwz %r7, 676(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3124(%r6)
	lwz %r5, 736(%r6)
	lwz %r7, 680(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3128(%r6)
	lwz %r5, 740(%r6)
	lwz %r7, 684(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3132(%r6)
	lwz %r5, 744(%r6)
	lwz %r7, 688(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3136(%r6)
	lwz %r5, 748(%r6)
	lwz %r7, 692(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3140(%r6)
	lwz %r5, 752(%r6)
	lwz %r7, 696(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3144(%r6)
	lwz %r5, 756(%r6)
	lwz %r7, 700(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3148(%r6)
	lwz %r5, 760(%r6)
	lwz %r7, 704(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3152(%r6)
	lwz %r5, 764(%r6)
	lwz %r7, 708(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3156(%r6)
	lwz %r5, 768(%r6)
	lwz %r7, 712(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3160(%r6)
	lwz %r5, 772(%r6)
	lwz %r7, 716(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3164(%r6)
	lwz %r5, 776(%r6)
	lwz %r7, 720(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3168(%r6)
	lwz %r5, 780(%r6)
	lwz %r7, 724(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3172(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 168(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3176(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 172(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3180(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 176(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3184(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 180(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3188(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 184(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3192(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 188(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3196(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 192(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3200(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 196(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3204(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 200(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3208(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 204(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3212(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 208(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3216(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 212(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3220(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 216(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3224(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 220(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3228(%r6)
	lwz %r7, 3288(%r6)
	stw %r7, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r7, 3292(%r6)
	stw %r7, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r7, 3296(%r6)
	stw %r7, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 3300(%r6)
	stw %r7, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 3304(%r6)
	stw %r7, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 3308(%r6)
	stw %r7, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 3312(%r6)
	stw %r7, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 3316(%r6)
	stw %r7, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 3320(%r6)
	stw %r7, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 3324(%r6)
	stw %r7, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 3328(%r6)
	stw %r7, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 3332(%r6)
	stw %r7, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 3336(%r6)
	stw %r7, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 3340(%r6)
	stw %r7, 220(%r6)
	stw %r7, 108(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	lwz %r8, 3288(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	lwz %r8, 3292(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	lwz %r8, 3296(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	lwz %r8, 3300(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	lwz %r8, 3304(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	lwz %r8, 3308(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	lwz %r8, 3312(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	lwz %r8, 3316(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	lwz %r8, 3320(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	lwz %r8, 3324(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	lwz %r8, 3328(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	lwz %r8, 3332(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	lwz %r8, 3336(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	lwz %r8, 3340(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r10
	std %r9, 3520(%r6)
	lbz %r7, 3344(%r6)
	li %r8, 127
	and %r8, %r7, %r8
	ld %r9, 3520(%r6)
	or %r9, %r9, %r8
	std %r9, 3520(%r6)
	rldicl %r7, %r7, 57, 7
	stb %r7, 3528(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 256(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 260(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 264(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 268(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 272(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 276(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
216:
	ld %r4, 168(%r9)
	li %r8, 0
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 216b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 284(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 280(%r6)
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 284(%r6)
	add %r7, %r7, %r8
	stw %r7, 284(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 288(%r6)
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 280(%r6)
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 284(%r6)
	add %r7, %r7, %r8
	stw %r7, 284(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 288(%r6)
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	ld %r7, 280(%r6)
	ld %r8, 224(%r6)
	subfc %r7, %r8, %r7
	std %r7, 392(%r6)
	ld %r7, 288(%r6)
	ld %r8, 232(%r6)
	subfe %r7, %r8, %r7
	std %r7, 400(%r6)
	ld %r7, 296(%r6)
	ld %r8, 240(%r6)
	subfe %r7, %r8, %r7
	std %r7, 408(%r6)
	ld %r7, 304(%r6)
	ld %r8, 248(%r6)
	subfe %r7, %r8, %r7
	std %r7, 416(%r6)
	ld %r7, 312(%r6)
	ld %r8, 256(%r6)
	subfe %r7, %r8, %r7
	std %r7, 424(%r6)
	ld %r7, 320(%r6)
	ld %r8, 264(%r6)
	subfe %r7, %r8, %r7
	std %r7, 432(%r6)
	ld %r7, 328(%r6)
	ld %r8, 272(%r6)
	subfe %r7, %r8, %r7
	std %r7, 440(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 392(%r6)
	subfc %r7, %r4, %r7
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	subfe %r7, %r8, %r7
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	subfe %r7, %r8, %r7
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	subfe %r7, %r5, %r7
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	subfe %r7, %r8, %r7
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	subfe %r7, %r8, %r7
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	subfe %r7, %r8, %r7
	std %r7, 440(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 392(%r6)
	subfc %r7, %r4, %r7
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	subfe %r7, %r8, %r7
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	subfe %r7, %r8, %r7
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	subfe %r7, %r5, %r7
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	subfe %r7, %r8, %r7
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	subfe %r7, %r8, %r7
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	subfe %r7, %r8, %r7
	std %r7, 440(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
217:
	ld %r4, 336(%r9)
	li %r8, 0
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 320(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 328(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 217b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	ld %r7, 448(%r6)
	ld %r8, 224(%r6)
	subfc %r7, %r8, %r7
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	ld %r8, 232(%r6)
	subfe %r7, %r8, %r7
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	ld %r8, 240(%r6)
	subfe %r7, %r8, %r7
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	ld %r8, 248(%r6)
	subfe %r7, %r8, %r7
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	ld %r8, 256(%r6)
	subfe %r7, %r8, %r7
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	ld %r8, 264(%r6)
	subfe %r7, %r8, %r7
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	ld %r8, 272(%r6)
	subfe %r7, %r8, %r7
	std %r7, 496(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 448(%r6)
	subfc %r7, %r4, %r7
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	subfe %r7, %r8, %r7
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	subfe %r7, %r8, %r7
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	subfe %r7, %r5, %r7
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	subfe %r7, %r8, %r7
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	subfe %r7, %r8, %r7
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	subfe %r7, %r8, %r7
	std %r7, 496(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 448(%r6)
	subfc %r7, %r4, %r7
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	subfe %r7, %r8, %r7
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	subfe %r7, %r8, %r7
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	subfe %r7, %r5, %r7
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	subfe %r7, %r8, %r7
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	subfe %r7, %r8, %r7
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	subfe %r7, %r8, %r7
	std %r7, 496(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
218:
	ld %r4, 392(%r9)
	li %r8, 0
	ld %r5, 392(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 400(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 408(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 416(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 424(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 432(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 440(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 218b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
219:
	ld %r4, 504(%r9)
	li %r8, 0
	ld %r5, 392(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 400(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 408(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 416(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 424(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 432(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 440(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 219b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
220:
	ld %r4, 504(%r9)
	li %r8, 0
	ld %r5, 448(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 456(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 464(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 472(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 220b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
221:
	ld %r4, 392(%r9)
	li %r8, 0
	ld %r5, 448(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 456(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 464(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 472(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 221b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
222:
	ld %r4, 560(%r9)
	li %r8, 0
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 222b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
223:
	ld %r4, 504(%r9)
	li %r8, 0
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 223b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 112(%r6)
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 112(%r6)
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 1
	li %r5, 0
	stw %r4, 840(%r6)
	stw %r5, 844(%r6)
	stw %r5, 848(%r6)
	stw %r5, 852(%r6)
	stw %r5, 856(%r6)
	stw %r5, 860(%r6)
	stw %r5, 864(%r6)
	stw %r5, 868(%r6)
	stw %r5, 872(%r6)
	stw %r5, 876(%r6)
	stw %r5, 880(%r6)
	stw %r5, 884(%r6)
	stw %r5, 888(%r6)
	stw %r5, 892(%r6)
	li %r12, 446
224:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
225:
	ld %r4, 840(%r9)
	li %r8, 0
	ld %r5, 840(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 848(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 856(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 864(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 872(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 880(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 888(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 225b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r5, %r12, -222
	cmpldi %cr0, %r5, 0
	beq %cr0, 226f
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
228:
	ld %r4, 840(%r9)
	li %r8, 0
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 228b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	b 227f
226:
227:
	cmpldi %cr0, %r12, 0
	bne %cr0, 224b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
229:
	ld %r4, 504(%r9)
	li %r8, 0
	ld %r5, 840(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 848(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 856(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 864(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 872(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 880(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 888(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 229b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 672(%r6)
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 672(%r6)
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
230:
	ld %r4, 672(%r9)
	li %r8, 0
	ld %r5, 672(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 680(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 688(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 696(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 704(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 712(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 720(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 230b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
231:
	ld %r4, 448(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 231b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	ld %r7, 616(%r6)
	ld %r8, 392(%r6)
	subfc %r7, %r8, %r7
	std %r7, 56(%r6)
	ld %r7, 624(%r6)
	ld %r8, 400(%r6)
	subfe %r7, %r8, %r7
	std %r7, 64(%r6)
	ld %r7, 632(%r6)
	ld %r8, 408(%r6)
	subfe %r7, %r8, %r7
	std %r7, 72(%r6)
	ld %r7, 640(%r6)
	ld %r8, 416(%r6)
	subfe %r7, %r8, %r7
	std %r7, 80(%r6)
	ld %r7, 648(%r6)
	ld %r8, 424(%r6)
	subfe %r7, %r8, %r7
	std %r7, 88(%r6)
	ld %r7, 656(%r6)
	ld %r8, 432(%r6)
	subfe %r7, %r8, %r7
	std %r7, 96(%r6)
	ld %r7, 664(%r6)
	ld %r8, 440(%r6)
	subfe %r7, %r8, %r7
	std %r7, 104(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 56(%r6)
	subfc %r7, %r4, %r7
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	subfe %r7, %r8, %r7
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	subfe %r7, %r8, %r7
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	subfe %r7, %r5, %r7
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	subfe %r7, %r8, %r7
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	subfe %r7, %r8, %r7
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	subfe %r7, %r8, %r7
	std %r7, 104(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 56(%r6)
	subfc %r7, %r4, %r7
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	subfe %r7, %r8, %r7
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	subfe %r7, %r8, %r7
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	subfe %r7, %r5, %r7
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	subfe %r7, %r8, %r7
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	subfe %r7, %r8, %r7
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	subfe %r7, %r8, %r7
	std %r7, 104(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	or %r10, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r10
	std %r9, 3520(%r6)
	li %r11, 0
	lwz %r5, 672(%r6)
	lwz %r7, 672(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 56(%r6)
	lwz %r5, 676(%r6)
	lwz %r7, 676(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 60(%r6)
	lwz %r5, 680(%r6)
	lwz %r7, 680(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 64(%r6)
	lwz %r5, 684(%r6)
	lwz %r7, 684(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 68(%r6)
	lwz %r5, 688(%r6)
	lwz %r7, 688(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 72(%r6)
	lwz %r5, 692(%r6)
	lwz %r7, 692(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 76(%r6)
	lwz %r5, 696(%r6)
	lwz %r7, 696(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 80(%r6)
	lwz %r5, 700(%r6)
	lwz %r7, 700(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 84(%r6)
	lwz %r5, 704(%r6)
	lwz %r7, 704(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 88(%r6)
	lwz %r5, 708(%r6)
	lwz %r7, 708(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 92(%r6)
	lwz %r5, 712(%r6)
	lwz %r7, 712(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 96(%r6)
	lwz %r5, 716(%r6)
	lwz %r7, 716(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 100(%r6)
	lwz %r5, 720(%r6)
	lwz %r7, 720(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 104(%r6)
	lwz %r5, 724(%r6)
	lwz %r7, 724(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 108(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	or %r10, %r10, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	lbz %r7, 3528(%r6)
	and %r8, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r8
	std %r9, 3520(%r6)
	ld %r7, 672(%r6)
	ld %r8, 672(%r6)
	subfc %r7, %r8, %r7
	std %r7, 616(%r6)
	ld %r7, 680(%r6)
	ld %r8, 680(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 688(%r6)
	ld %r8, 688(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 696(%r6)
	ld %r8, 696(%r6)
	subfe %r7, %r8, %r7
	std %r7, 640(%r6)
	ld %r7, 704(%r6)
	ld %r8, 704(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 712(%r6)
	ld %r8, 712(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 720(%r6)
	ld %r8, 720(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 616(%r6)
	subfc %r7, %r4, %r7
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	subfe %r7, %r5, %r7
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 616(%r6)
	subfc %r7, %r4, %r7
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	subfe %r7, %r5, %r7
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	ld %r7, 616(%r6)
	ld %r8, 672(%r6)
	subfc %r7, %r8, %r7
	std %r7, 728(%r6)
	ld %r7, 624(%r6)
	ld %r8, 680(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 632(%r6)
	ld %r8, 688(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 640(%r6)
	ld %r8, 696(%r6)
	subfe %r7, %r8, %r7
	std %r7, 752(%r6)
	ld %r7, 648(%r6)
	ld %r8, 704(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 656(%r6)
	ld %r8, 712(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 664(%r6)
	ld %r8, 720(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	lbz %r8, 0(%r3)
	li %r9, 1
	and %r8, %r8, %r9
	lbz %r7, 3528(%r6)
	xor %r8, %r8, %r7
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 728(%r6)
	lwz %r7, 672(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3008(%r6)
	lwz %r5, 732(%r6)
	lwz %r7, 676(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3012(%r6)
	lwz %r5, 736(%r6)
	lwz %r7, 680(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3016(%r6)
	lwz %r5, 740(%r6)
	lwz %r7, 684(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3020(%r6)
	lwz %r5, 744(%r6)
	lwz %r7, 688(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3024(%r6)
	lwz %r5, 748(%r6)
	lwz %r7, 692(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3028(%r6)
	lwz %r5, 752(%r6)
	lwz %r7, 696(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3032(%r6)
	lwz %r5, 756(%r6)
	lwz %r7, 700(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3036(%r6)
	lwz %r5, 760(%r6)
	lwz %r7, 704(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3040(%r6)
	lwz %r5, 764(%r6)
	lwz %r7, 708(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3044(%r6)
	lwz %r5, 768(%r6)
	lwz %r7, 712(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3048(%r6)
	lwz %r5, 772(%r6)
	lwz %r7, 716(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3052(%r6)
	lwz %r5, 776(%r6)
	lwz %r7, 720(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3056(%r6)
	lwz %r5, 780(%r6)
	lwz %r7, 724(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3060(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 168(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3064(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 172(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3068(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 176(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3072(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 180(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3076(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 184(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3080(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 188(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3084(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 192(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3088(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 196(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3092(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 200(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3096(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 204(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3100(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 208(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3104(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 212(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3108(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 216(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3112(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 220(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3116(%r6)
	lwz %r7, 3402(%r6)
	stw %r7, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r7, 3406(%r6)
	stw %r7, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r7, 3410(%r6)
	stw %r7, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 3414(%r6)
	stw %r7, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 3418(%r6)
	stw %r7, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 3422(%r6)
	stw %r7, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 3426(%r6)
	stw %r7, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 3430(%r6)
	stw %r7, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 3434(%r6)
	stw %r7, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 3438(%r6)
	stw %r7, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 3442(%r6)
	stw %r7, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 3446(%r6)
	stw %r7, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 3450(%r6)
	stw %r7, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 3454(%r6)
	stw %r7, 220(%r6)
	stw %r7, 108(%r6)
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	ld %r9, 3520(%r6)
	or %r9, %r9, %r8
	std %r9, 3520(%r6)
	lbz %r7, 3458(%r6)
	ld %r9, 3520(%r6)
	or %r9, %r9, %r7
	std %r9, 3520(%r6)
	addi %r9, %r6, 0
	li %r11, 468
	li %r7, 0
232:
	stb %r7, 1064(%r9)
	stb %r7, 1065(%r9)
	stb %r7, 1066(%r9)
	stb %r7, 1067(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 232b
	addi %r9, %r6, 0
	addi %r4, %r6, 3402
	li %r11, 57
233:
	lbz %r7, 0(%r4)
	rldicr %r8, %r7, 63, 0
	rldicl %r8, %r8, 1, 63
	stb %r8, 1064(%r9)
	rldicr %r8, %r7, 62, 1
	rldicl %r8, %r8, 1, 63
	stb %r8, 1068(%r9)
	rldicr %r8, %r7, 61, 2
	rldicl %r8, %r8, 1, 63
	stb %r8, 1072(%r9)
	rldicr %r8, %r7, 60, 3
	rldicl %r8, %r8, 1, 63
	stb %r8, 1076(%r9)
	rldicr %r8, %r7, 59, 4
	rldicl %r8, %r8, 1, 63
	stb %r8, 1080(%r9)
	rldicr %r8, %r7, 58, 5
	rldicl %r8, %r8, 1, 63
	stb %r8, 1084(%r9)
	rldicr %r8, %r7, 57, 6
	rldicl %r8, %r8, 1, 63
	stb %r8, 1088(%r9)
	rldicr %r8, %r7, 56, 7
	rldicl %r8, %r8, 1, 63
	stb %r8, 1092(%r9)
	addi %r4, %r4, 1
	addi %r9, %r9, 32
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 233b
	addi %r9, %r6, 0
	addi %r4, %r6, 3459
	li %r11, 57
234:
	lbz %r7, 0(%r4)
	rldicr %r8, %r7, 63, 0
	rldicl %r8, %r8, 1, 63
	stb %r8, 1065(%r9)
	rldicr %r8, %r7, 62, 1
	rldicl %r8, %r8, 1, 63
	stb %r8, 1069(%r9)
	rldicr %r8, %r7, 61, 2
	rldicl %r8, %r8, 1, 63
	stb %r8, 1073(%r9)
	rldicr %r8, %r7, 60, 3
	rldicl %r8, %r8, 1, 63
	stb %r8, 1077(%r9)
	rldicr %r8, %r7, 59, 4
	rldicl %r8, %r8, 1, 63
	stb %r8, 1081(%r9)
	rldicr %r8, %r7, 58, 5
	rldicl %r8, %r8, 1, 63
	stb %r8, 1085(%r9)
	rldicr %r8, %r7, 57, 6
	rldicl %r8, %r8, 1, 63
	stb %r8, 1089(%r9)
	rldicr %r8, %r7, 56, 7
	rldicl %r8, %r8, 1, 63
	stb %r8, 1093(%r9)
	addi %r4, %r4, 1
	addi %r9, %r9, 32
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 234b
	addi %r9, %r6, 0
	li %r10, 16
	li %r11, 464
235:
	lbz %r7, 1064(%r9)
	lbz %r8, 1068(%r9)
	rldicr %r8, %r8, 1, 62
	or %r7, %r7, %r8
	lbz %r8, 1072(%r9)
	rldicr %r8, %r8, 2, 61
	or %r7, %r7, %r8
	lbz %r8, 1076(%r9)
	rldicr %r8, %r8, 3, 60
	or %r7, %r7, %r8
	lbz %r8, 1080(%r9)
	rldicr %r8, %r8, 4, 59
	or %r7, %r7, %r8
	add %r8, %r7, %r10
	addi %r8, %r8, 16
	li %r4, 31
	and %r8, %r8, %r4
	li %r4, 1
	and %r5, %r8, %r4
	rldicl %r12, %r8, 60, 4
	rldicr %r12, %r12, 5, 58
	subf %r12, %r12, %r8
	li %r0, 0
	subf %r0, %r5, %r0
	and %r12, %r12, %r0
	stb %r12, 1066(%r9)
	and %r5, %r7, %r4
	add %r10, %r10, %r5
	addi %r10, %r10, 16
	subf %r10, %r12, %r10
	rldicl %r10, %r10, 63, 1
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 235b
	addi %r9, %r6, 0
	li %r10, 16
	li %r11, 464
236:
	lbz %r7, 1065(%r9)
	lbz %r8, 1069(%r9)
	rldicr %r8, %r8, 1, 62
	or %r7, %r7, %r8
	lbz %r8, 1073(%r9)
	rldicr %r8, %r8, 2, 61
	or %r7, %r7, %r8
	lbz %r8, 1077(%r9)
	rldicr %r8, %r8, 3, 60
	or %r7, %r7, %r8
	lbz %r8, 1081(%r9)
	rldicr %r8, %r8, 4, 59
	or %r7, %r7, %r8
	add %r8, %r7, %r10
	addi %r8, %r8, 16
	li %r4, 31
	and %r8, %r8, %r4
	li %r4, 1
	and %r5, %r8, %r4
	rldicl %r12, %r8, 60, 4
	rldicr %r12, %r12, 5, 58
	subf %r12, %r12, %r8
	li %r0, 0
	subf %r0, %r5, %r0
	and %r12, %r12, %r0
	stb %r12, 1067(%r9)
	and %r5, %r7, %r4
	add %r10, %r10, %r5
	addi %r10, %r10, 16
	subf %r10, %r12, %r10
	rldicl %r10, %r10, 63, 1
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 236b
	ld %r7, 3008(%r6)
	std %r7, 56(%r6)
	ld %r7, 3016(%r6)
	std %r7, 64(%r6)
	ld %r7, 3024(%r6)
	std %r7, 72(%r6)
	ld %r7, 3032(%r6)
	std %r7, 80(%r6)
	ld %r7, 3040(%r6)
	std %r7, 88(%r6)
	ld %r7, 3048(%r6)
	std %r7, 96(%r6)
	ld %r7, 3056(%r6)
	std %r7, 104(%r6)
	ld %r7, 3064(%r6)
	std %r7, 0(%r6)
	ld %r7, 3072(%r6)
	std %r7, 8(%r6)
	ld %r7, 3080(%r6)
	std %r7, 16(%r6)
	ld %r7, 3088(%r6)
	std %r7, 24(%r6)
	ld %r7, 3096(%r6)
	std %r7, 32(%r6)
	ld %r7, 3104(%r6)
	std %r7, 40(%r6)
	ld %r7, 3112(%r6)
	std %r7, 48(%r6)
	ld %r7, 3232(%r6)
	std %r7, 112(%r6)
	ld %r7, 3240(%r6)
	std %r7, 120(%r6)
	ld %r7, 3248(%r6)
	std %r7, 128(%r6)
	ld %r7, 3256(%r6)
	std %r7, 136(%r6)
	ld %r7, 3264(%r6)
	std %r7, 144(%r6)
	ld %r7, 3272(%r6)
	std %r7, 152(%r6)
	ld %r7, 3280(%r6)
	std %r7, 160(%r6)
	ld %r7, 56(%r6)
	std %r7, 4160(%r6)
	ld %r7, 64(%r6)
	std %r7, 4168(%r6)
	ld %r7, 72(%r6)
	std %r7, 4176(%r6)
	ld %r7, 80(%r6)
	std %r7, 4184(%r6)
	ld %r7, 88(%r6)
	std %r7, 4192(%r6)
	ld %r7, 96(%r6)
	std %r7, 4200(%r6)
	ld %r7, 104(%r6)
	std %r7, 4208(%r6)
	ld %r7, 0(%r6)
	std %r7, 4216(%r6)
	ld %r7, 8(%r6)
	std %r7, 4224(%r6)
	ld %r7, 16(%r6)
	std %r7, 4232(%r6)
	ld %r7, 24(%r6)
	std %r7, 4240(%r6)
	ld %r7, 32(%r6)
	std %r7, 4248(%r6)
	ld %r7, 40(%r6)
	std %r7, 4256(%r6)
	ld %r7, 48(%r6)
	std %r7, 4264(%r6)
	ld %r7, 112(%r6)
	std %r7, 4272(%r6)
	ld %r7, 120(%r6)
	std %r7, 4280(%r6)
	ld %r7, 128(%r6)
	std %r7, 4288(%r6)
	ld %r7, 136(%r6)
	std %r7, 4296(%r6)
	ld %r7, 144(%r6)
	std %r7, 4304(%r6)
	ld %r7, 152(%r6)
	std %r7, 4312(%r6)
	ld %r7, 160(%r6)
	std %r7, 4320(%r6)
	bl {vg_ed448_r32_double}
	ld %r7, 56(%r6)
	std %r7, 168(%r6)
	ld %r7, 64(%r6)
	std %r7, 176(%r6)
	ld %r7, 72(%r6)
	std %r7, 184(%r6)
	ld %r7, 80(%r6)
	std %r7, 192(%r6)
	ld %r7, 88(%r6)
	std %r7, 200(%r6)
	ld %r7, 96(%r6)
	std %r7, 208(%r6)
	ld %r7, 104(%r6)
	std %r7, 216(%r6)
	ld %r7, 0(%r6)
	std %r7, 224(%r6)
	ld %r7, 8(%r6)
	std %r7, 232(%r6)
	ld %r7, 16(%r6)
	std %r7, 240(%r6)
	ld %r7, 24(%r6)
	std %r7, 248(%r6)
	ld %r7, 32(%r6)
	std %r7, 256(%r6)
	ld %r7, 40(%r6)
	std %r7, 264(%r6)
	ld %r7, 48(%r6)
	std %r7, 272(%r6)
	ld %r7, 112(%r6)
	std %r7, 280(%r6)
	ld %r7, 120(%r6)
	std %r7, 288(%r6)
	ld %r7, 128(%r6)
	std %r7, 296(%r6)
	ld %r7, 136(%r6)
	std %r7, 304(%r6)
	ld %r7, 144(%r6)
	std %r7, 312(%r6)
	ld %r7, 152(%r6)
	std %r7, 320(%r6)
	ld %r7, 160(%r6)
	std %r7, 328(%r6)
	ld %r7, 4160(%r6)
	std %r7, 56(%r6)
	ld %r7, 4168(%r6)
	std %r7, 64(%r6)
	ld %r7, 4176(%r6)
	std %r7, 72(%r6)
	ld %r7, 4184(%r6)
	std %r7, 80(%r6)
	ld %r7, 4192(%r6)
	std %r7, 88(%r6)
	ld %r7, 4200(%r6)
	std %r7, 96(%r6)
	ld %r7, 4208(%r6)
	std %r7, 104(%r6)
	ld %r7, 4216(%r6)
	std %r7, 0(%r6)
	ld %r7, 4224(%r6)
	std %r7, 8(%r6)
	ld %r7, 4232(%r6)
	std %r7, 16(%r6)
	ld %r7, 4240(%r6)
	std %r7, 24(%r6)
	ld %r7, 4248(%r6)
	std %r7, 32(%r6)
	ld %r7, 4256(%r6)
	std %r7, 40(%r6)
	ld %r7, 4264(%r6)
	std %r7, 48(%r6)
	ld %r7, 4272(%r6)
	std %r7, 112(%r6)
	ld %r7, 4280(%r6)
	std %r7, 120(%r6)
	ld %r7, 4288(%r6)
	std %r7, 128(%r6)
	ld %r7, 4296(%r6)
	std %r7, 136(%r6)
	ld %r7, 4304(%r6)
	std %r7, 144(%r6)
	ld %r7, 4312(%r6)
	std %r7, 152(%r6)
	ld %r7, 4320(%r6)
	std %r7, 160(%r6)
	li %r14, 7
237:
	bl {vg_ed448_r32_add}
	li %r4, 8
	subf %r4, %r14, %r4
	rldicr %r12, %r4, 7, 56
	rldicr %r5, %r4, 5, 58
	add %r12, %r12, %r5
	rldicr %r5, %r4, 3, 60
	add %r12, %r12, %r5
	add %r12, %r12, %r6
	ld %r7, 392(%r6)
	std %r7, 4160(%r12)
	ld %r7, 400(%r6)
	std %r7, 4168(%r12)
	ld %r7, 408(%r6)
	std %r7, 4176(%r12)
	ld %r7, 416(%r6)
	std %r7, 4184(%r12)
	ld %r7, 424(%r6)
	std %r7, 4192(%r12)
	ld %r7, 432(%r6)
	std %r7, 4200(%r12)
	ld %r7, 440(%r6)
	std %r7, 4208(%r12)
	ld %r7, 448(%r6)
	std %r7, 4216(%r12)
	ld %r7, 456(%r6)
	std %r7, 4224(%r12)
	ld %r7, 464(%r6)
	std %r7, 4232(%r12)
	ld %r7, 472(%r6)
	std %r7, 4240(%r12)
	ld %r7, 480(%r6)
	std %r7, 4248(%r12)
	ld %r7, 488(%r6)
	std %r7, 4256(%r12)
	ld %r7, 496(%r6)
	std %r7, 4264(%r12)
	ld %r7, 504(%r6)
	std %r7, 4272(%r12)
	ld %r7, 512(%r6)
	std %r7, 4280(%r12)
	ld %r7, 520(%r6)
	std %r7, 4288(%r12)
	ld %r7, 528(%r6)
	std %r7, 4296(%r12)
	ld %r7, 536(%r6)
	std %r7, 4304(%r12)
	ld %r7, 544(%r6)
	std %r7, 4312(%r12)
	ld %r7, 552(%r6)
	std %r7, 4320(%r12)
	ld %r7, 392(%r6)
	std %r7, 56(%r6)
	ld %r7, 400(%r6)
	std %r7, 64(%r6)
	ld %r7, 408(%r6)
	std %r7, 72(%r6)
	ld %r7, 416(%r6)
	std %r7, 80(%r6)
	ld %r7, 424(%r6)
	std %r7, 88(%r6)
	ld %r7, 432(%r6)
	std %r7, 96(%r6)
	ld %r7, 440(%r6)
	std %r7, 104(%r6)
	ld %r7, 448(%r6)
	std %r7, 0(%r6)
	ld %r7, 456(%r6)
	std %r7, 8(%r6)
	ld %r7, 464(%r6)
	std %r7, 16(%r6)
	ld %r7, 472(%r6)
	std %r7, 24(%r6)
	ld %r7, 480(%r6)
	std %r7, 32(%r6)
	ld %r7, 488(%r6)
	std %r7, 40(%r6)
	ld %r7, 496(%r6)
	std %r7, 48(%r6)
	ld %r7, 504(%r6)
	std %r7, 112(%r6)
	ld %r7, 512(%r6)
	std %r7, 120(%r6)
	ld %r7, 520(%r6)
	std %r7, 128(%r6)
	ld %r7, 528(%r6)
	std %r7, 136(%r6)
	ld %r7, 536(%r6)
	std %r7, 144(%r6)
	ld %r7, 544(%r6)
	std %r7, 152(%r6)
	ld %r7, 552(%r6)
	std %r7, 160(%r6)
	addi %r14, %r14, -1
	cmpldi %cr0, %r14, 0
	bne %cr0, 237b
	lis %r7, -14580
	ori %r7, %r7, 49246
	stw %r7, 5504(%r6)
	lis %r7, 9766
	ori %r7, %r7, 43051
	stw %r7, 5508(%r6)
	lis %r7, -29952
	ori %r7, %r7, 37774
	stw %r7, 5512(%r6)
	lis %r7, 17211
	ori %r7, %r7, 32993
	stw %r7, 5516(%r6)
	lis %r7, 10934
	ori %r7, %r7, 25873
	stw %r7, 5520(%r6)
	lis %r7, 4782
	ori %r7, %r7, 6903
	stw %r7, 5524(%r6)
	lis %r7, -23597
	ori %r7, %r7, 42084
	stw %r7, 5528(%r6)
	lis %r7, -5523
	ori %r7, %r7, 58148
	stw %r7, 5532(%r6)
	lis %r7, 18191
	ori %r7, %r7, 5991
	stw %r7, 5536(%r6)
	lis %r7, -25068
	ori %r7, %r7, 25968
	stw %r7, 5540(%r6)
	lis %r7, 8895
	ori %r7, %r7, 14042
	stw %r7, 5544(%r6)
	lis %r7, 8733
	ori %r7, %r7, 5542
	stw %r7, 5548(%r6)
	lis %r7, 27629
	ori %r7, %r7, 3565
	stw %r7, 5552(%r6)
	lis %r7, 20249
	ori %r7, %r7, 28870
	stw %r7, 5556(%r6)
	lis %r7, -3536
	ori %r7, %r7, 64020
	stw %r7, 5560(%r6)
	lis %r7, -26616
	ori %r7, %r7, 31067
	stw %r7, 5564(%r6)
	lis %r7, 20183
	ori %r7, %r7, 51373
	stw %r7, 5568(%r6)
	lis %r7, -579
	ori %r7, %r7, 4908
	stw %r7, 5572(%r6)
	lis %r7, -6532
	ori %r7, %r7, 14788
	stw %r7, 5576(%r6)
	lis %r7, 15059
	ori %r7, %r7, 65308
	stw %r7, 5580(%r6)
	lis %r7, 1440
	ori %r7, %r7, 49879
	stw %r7, 5584(%r6)
	lis %r7, -30856
	ori %r7, %r7, 39966
	stw %r7, 5588(%r6)
	lis %r7, 27811
	ori %r7, %r7, 38976
	stw %r7, 5592(%r6)
	lis %r7, 19434
	ori %r7, %r7, 29555
	stw %r7, 5596(%r6)
	lis %r7, 22217
	ori %r7, %r7, 51042
	stw %r7, 5600(%r6)
	lis %r7, -30602
	ori %r7, %r7, 8247
	stw %r7, 5604(%r6)
	lis %r7, 28342
	ori %r7, %r7, 48164
	stw %r7, 5608(%r6)
	lis %r7, 26943
	ori %r7, %r7, 18033
	stw %r7, 5612(%r6)
	lis %r7, -30977
	ori %r7, %r7, 12175
	stw %r7, 5616(%r6)
	lis %r7, 22312
	ori %r7, %r7, 5938
	stw %r7, 5620(%r6)
	lis %r7, 18013
	ori %r7, %r7, 43095
	stw %r7, 5624(%r6)
	lis %r7, -6046
	ori %r7, %r7, 46953
	stw %r7, 5628(%r6)
	lis %r7, -2521
	ori %r7, %r7, 8150
	stw %r7, 5632(%r6)
	lis %r7, -9559
	ori %r7, %r7, 52215
	stw %r7, 5636(%r6)
	lis %r7, 19007
	ori %r7, %r7, 53224
	stw %r7, 5640(%r6)
	lis %r7, -7494
	ori %r7, %r7, 1914
	stw %r7, 5644(%r6)
	lis %r7, -29478
	ori %r7, %r7, 33479
	stw %r7, 5648(%r6)
	lis %r7, 12836
	ori %r7, %r7, 7051
	stw %r7, 5652(%r6)
	lis %r7, 27830
	ori %r7, %r7, 37939
	stw %r7, 5656(%r6)
	lis %r7, 21949
	ori %r7, %r7, 25649
	stw %r7, 5660(%r6)
	lis %r7, -28408
	ori %r7, %r7, 44900
	stw %r7, 5664(%r6)
	lis %r7, 2149
	ori %r7, %r7, 34923
	stw %r7, 5668(%r6)
	lis %r7, 22670
	ori %r7, %r7, 55036
	stw %r7, 5672(%r6)
	lis %r7, -18398
	ori %r7, %r7, 44051
	stw %r7, 5676(%r6)
	lis %r7, -304
	ori %r7, %r7, 11695
	stw %r7, 5680(%r6)
	lis %r7, -16390
	ori %r7, %r7, 39528
	stw %r7, 5684(%r6)
	lis %r7, -9369
	ori %r7, %r7, 26608
	stw %r7, 5688(%r6)
	lis %r7, -17606
	ori %r7, %r7, 13083
	stw %r7, 5692(%r6)
	lis %r7, -5042
	ori %r7, %r7, 7512
	stw %r7, 5696(%r6)
	lis %r7, -796
	ori %r7, %r7, 15490
	stw %r7, 5700(%r6)
	lis %r7, 9046
	ori %r7, %r7, 50105
	stw %r7, 5704(%r6)
	lis %r7, -26038
	ori %r7, %r7, 36245
	stw %r7, 5708(%r6)
	lis %r7, -11206
	ori %r7, %r7, 42564
	stw %r7, 5712(%r6)
	lis %r7, 1739
	ori %r7, %r7, 55930
	stw %r7, 5716(%r6)
	lis %r7, -10990
	ori %r7, %r7, 23799
	stw %r7, 5720(%r6)
	lis %r7, -8187
	ori %r7, %r7, 43227
	stw %r7, 5724(%r6)
	lis %r7, -28157
	ori %r7, %r7, 52
	stw %r7, 5728(%r6)
	lis %r7, -12119
	ori %r7, %r7, 40208
	stw %r7, 5732(%r6)
	lis %r7, -4154
	ori %r7, %r7, 63824
	stw %r7, 5736(%r6)
	lis %r7, -3973
	ori %r7, %r7, 11660
	stw %r7, 5740(%r6)
	lis %r7, -28148
	ori %r7, %r7, 15510
	stw %r7, 5744(%r6)
	lis %r7, -29760
	ori %r7, %r7, 54650
	stw %r7, 5748(%r6)
	lis %r7, -27256
	ori %r7, %r7, 4736
	stw %r7, 5752(%r6)
	lis %r7, 22231
	ori %r7, %r7, 25064
	stw %r7, 5756(%r6)
	lis %r7, -31390
	ori %r7, %r7, 44455
	stw %r7, 5760(%r6)
	lis %r7, -32565
	ori %r7, %r7, 53106
	stw %r7, 5764(%r6)
	lis %r7, -4683
	ori %r7, %r7, 3567
	stw %r7, 5768(%r6)
	lis %r7, 11175
	ori %r7, %r7, 24606
	stw %r7, 5772(%r6)
	lis %r7, -23411
	ori %r7, %r7, 51982
	stw %r7, 5776(%r6)
	lis %r7, 31391
	ori %r7, %r7, 37685
	stw %r7, 5780(%r6)
	lis %r7, 29428
	ori %r7, %r7, 13803
	stw %r7, 5784(%r6)
	lis %r7, 17332
	ori %r7, %r7, 29460
	stw %r7, 5788(%r6)
	lis %r7, -30689
	ori %r7, %r7, 8788
	stw %r7, 5792(%r6)
	lis %r7, 22592
	ori %r7, %r7, 21778
	stw %r7, 5796(%r6)
	lis %r7, 22994
	ori %r7, %r7, 45884
	stw %r7, 5800(%r6)
	lis %r7, 10199
	ori %r7, %r7, 42222
	stw %r7, 5804(%r6)
	lis %r7, -18792
	ori %r7, %r7, 369
	stw %r7, 5808(%r6)
	lis %r7, -10139
	ori %r7, %r7, 20983
	stw %r7, 5812(%r6)
	lis %r7, 15025
	ori %r7, %r7, 36814
	stw %r7, 5816(%r6)
	lis %r7, 9740
	ori %r7, %r7, 41346
	stw %r7, 5820(%r6)
	lis %r7, -680
	ori %r7, %r7, 2782
	stw %r7, 5824(%r6)
	lis %r7, -18160
	ori %r7, %r7, 40164
	stw %r7, 5828(%r6)
	lis %r7, 9495
	ori %r7, %r7, 60883
	stw %r7, 5832(%r6)
	lis %r7, -20995
	ori %r7, %r7, 29978
	stw %r7, 5836(%r6)
	lis %r7, -12619
	ori %r7, %r7, 60151
	stw %r7, 5840(%r6)
	lis %r7, -10273
	ori %r7, %r7, 38247
	stw %r7, 5844(%r6)
	lis %r7, 27463
	ori %r7, %r7, 35527
	stw %r7, 5848(%r6)
	lis %r7, 28171
	ori %r7, %r7, 4362
	stw %r7, 5852(%r6)
	lis %r7, 13136
	ori %r7, %r7, 5232
	stw %r7, 5856(%r6)
	lis %r7, -19038
	ori %r7, %r7, 2349
	stw %r7, 5860(%r6)
	lis %r7, 3577
	ori %r7, %r7, 51120
	stw %r7, 5864(%r6)
	lis %r7, -10904
	ori %r7, %r7, 59012
	stw %r7, 5868(%r6)
	lis %r7, -25670
	ori %r7, %r7, 16931
	stw %r7, 5872(%r6)
	lis %r7, -3368
	ori %r7, %r7, 50033
	stw %r7, 5876(%r6)
	lis %r7, -28234
	ori %r7, %r7, 55178
	stw %r7, 5880(%r6)
	lis %r7, 18043
	ori %r7, %r7, 39506
	stw %r7, 5884(%r6)
	lis %r7, -14181
	ori %r7, %r7, 61303
	stw %r7, 5888(%r6)
	lis %r7, 1943
	ori %r7, %r7, 18661
	stw %r7, 5892(%r6)
	lis %r7, -21076
	ori %r7, %r7, 14207
	stw %r7, 5896(%r6)
	lis %r7, 2530
	ori %r7, %r7, 3391
	stw %r7, 5900(%r6)
	lis %r7, 26263
	ori %r7, %r7, 11100
	stw %r7, 5904(%r6)
	lis %r7, -17481
	ori %r7, %r7, 13544
	stw %r7, 5908(%r6)
	lis %r7, 26746
	ori %r7, %r7, 15424
	stw %r7, 5912(%r6)
	lis %r7, 12164
	ori %r7, %r7, 51672
	stw %r7, 5916(%r6)
	lis %r7, 31545
	ori %r7, %r7, 18173
	stw %r7, 5920(%r6)
	lis %r7, -13704
	ori %r7, %r7, 62734
	stw %r7, 5924(%r6)
	lis %r7, 31184
	ori %r7, %r7, 3648
	stw %r7, 5928(%r6)
	lis %r7, -27583
	ori %r7, %r7, 32369
	stw %r7, 5932(%r6)
	lis %r7, 13699
	ori %r7, %r7, 47221
	stw %r7, 5936(%r6)
	lis %r7, 29555
	ori %r7, %r7, 48306
	stw %r7, 5940(%r6)
	lis %r7, -28419
	ori %r7, %r7, 27036
	stw %r7, 5944(%r6)
	lis %r7, 32222
	ori %r7, %r7, 55868
	stw %r7, 5948(%r6)
	lis %r7, 30379
	ori %r7, %r7, 26731
	stw %r7, 5952(%r6)
	lis %r7, 31037
	ori %r7, %r7, 3567
	stw %r7, 5956(%r6)
	lis %r7, 32452
	ori %r7, %r7, 40828
	stw %r7, 5960(%r6)
	lis %r7, -30227
	ori %r7, %r7, 6726
	stw %r7, 5964(%r6)
	lis %r7, 21492
	ori %r7, %r7, 64649
	stw %r7, 5968(%r6)
	lis %r7, 12448
	ori %r7, %r7, 55614
	stw %r7, 5972(%r6)
	lis %r7, 4126
	ori %r7, %r7, 13380
	stw %r7, 5976(%r6)
	lis %r7, 6317
	ori %r7, %r7, 17646
	stw %r7, 5980(%r6)
	lis %r7, 13475
	ori %r7, %r7, 44659
	stw %r7, 5984(%r6)
	lis %r7, 27866
	ori %r7, %r7, 57809
	stw %r7, 5988(%r6)
	lis %r7, -21171
	ori %r7, %r7, 44794
	stw %r7, 5992(%r6)
	lis %r7, -29481
	ori %r7, %r7, 55332
	stw %r7, 5996(%r6)
	lis %r7, -10876
	ori %r7, %r7, 64682
	stw %r7, 6000(%r6)
	lis %r7, -4330
	ori %r7, %r7, 20686
	stw %r7, 6004(%r6)
	lis %r7, 29940
	ori %r7, %r7, 30031
	stw %r7, 6008(%r6)
	lis %r7, -29785
	ori %r7, %r7, 19958
	stw %r7, 6012(%r6)
	lis %r7, -5490
	ori %r7, %r7, 62459
	stw %r7, 6016(%r6)
	lis %r7, 4416
	ori %r7, %r7, 62764
	stw %r7, 6020(%r6)
	lis %r7, -15571
	ori %r7, %r7, 17047
	stw %r7, 6024(%r6)
	lis %r7, 9583
	ori %r7, %r7, 47943
	stw %r7, 6028(%r6)
	lis %r7, 14620
	ori %r7, %r7, 5594
	stw %r7, 6032(%r6)
	lis %r7, -17824
	ori %r7, %r7, 22129
	stw %r7, 6036(%r6)
	lis %r7, -17983
	ori %r7, %r7, 26106
	stw %r7, 6040(%r6)
	lis %r7, -29592
	ori %r7, %r7, 31123
	stw %r7, 6044(%r6)
	lis %r7, -22451
	ori %r7, %r7, 62033
	stw %r7, 6048(%r6)
	lis %r7, -20614
	ori %r7, %r7, 52181
	stw %r7, 6052(%r6)
	lis %r7, -28910
	ori %r7, %r7, 44589
	stw %r7, 6056(%r6)
	lis %r7, 5472
	ori %r7, %r7, 46633
	stw %r7, 6060(%r6)
	lis %r7, 9549
	ori %r7, %r7, 49418
	stw %r7, 6064(%r6)
	lis %r7, -18193
	ori %r7, %r7, 19872
	stw %r7, 6068(%r6)
	lis %r7, -31147
	ori %r7, %r7, 37901
	stw %r7, 6072(%r6)
	lis %r7, 10568
	ori %r7, %r7, 25361
	stw %r7, 6076(%r6)
	lis %r7, 2836
	ori %r7, %r7, 38959
	stw %r7, 6080(%r6)
	lis %r7, 22557
	ori %r7, %r7, 47842
	stw %r7, 6084(%r6)
	lis %r7, 26553
	ori %r7, %r7, 14197
	stw %r7, 6088(%r6)
	lis %r7, 4175
	ori %r7, %r7, 20521
	stw %r7, 6092(%r6)
	lis %r7, 13378
	ori %r7, %r7, 12007
	stw %r7, 6096(%r6)
	lis %r7, 3509
	ori %r7, %r7, 4653
	stw %r7, 6100(%r6)
	lis %r7, -14784
	ori %r7, %r7, 23876
	stw %r7, 6104(%r6)
	lis %r7, -6803
	ori %r7, %r7, 29092
	stw %r7, 6108(%r6)
	lis %r7, 9224
	ori %r7, %r7, 61105
	stw %r7, 6112(%r6)
	lis %r7, -16622
	ori %r7, %r7, 43964
	stw %r7, 6116(%r6)
	lis %r7, 24598
	ori %r7, %r7, 44801
	stw %r7, 6120(%r6)
	lis %r7, -21748
	ori %r7, %r7, 51704
	stw %r7, 6124(%r6)
	lis %r7, 27327
	ori %r7, %r7, 15756
	stw %r7, 6128(%r6)
	lis %r7, -494
	ori %r7, %r7, 34870
	stw %r7, 6132(%r6)
	lis %r7, -8799
	ori %r7, %r7, 14894
	stw %r7, 6136(%r6)
	lis %r7, -12282
	ori %r7, %r7, 29829
	stw %r7, 6140(%r6)
	lis %r7, 14605
	ori %r7, %r7, 62981
	stw %r7, 6144(%r6)
	lis %r7, 1745
	ori %r7, %r7, 34807
	stw %r7, 6148(%r6)
	lis %r7, 8433
	ori %r7, %r7, 36696
	stw %r7, 6152(%r6)
	lis %r7, 255
	ori %r7, %r7, 3165
	stw %r7, 6156(%r6)
	lis %r7, 5939
	ori %r7, %r7, 10441
	stw %r7, 6160(%r6)
	lis %r7, 12417
	ori %r7, %r7, 9184
	stw %r7, 6164(%r6)
	lis %r7, 19442
	ori %r7, %r7, 64941
	stw %r7, 6168(%r6)
	lis %r7, 17107
	ori %r7, %r7, 23381
	stw %r7, 6172(%r6)
	lis %r7, -3329
	ori %r7, %r7, 45553
	stw %r7, 6176(%r6)
	lis %r7, 1280
	ori %r7, %r7, 37173
	stw %r7, 6180(%r6)
	lis %r7, -14360
	ori %r7, %r7, 63942
	stw %r7, 6184(%r6)
	lis %r7, -1446
	ori %r7, %r7, 2463
	stw %r7, 6188(%r6)
	lis %r7, 26586
	ori %r7, %r7, 25195
	stw %r7, 6192(%r6)
	lis %r7, 17493
	ori %r7, %r7, 11212
	stw %r7, 6196(%r6)
	lis %r7, -15994
	ori %r7, %r7, 53539
	stw %r7, 6200(%r6)
	lis %r7, 435
	ori %r7, %r7, 14817
	stw %r7, 6204(%r6)
	lis %r7, -14923
	ori %r7, %r7, 8997
	stw %r7, 6208(%r6)
	lis %r7, 17660
	ori %r7, %r7, 38664
	stw %r7, 6212(%r6)
	lis %r7, 10471
	ori %r7, %r7, 28837
	stw %r7, 6216(%r6)
	lis %r7, -17746
	ori %r7, %r7, 49641
	stw %r7, 6220(%r6)
	lis %r7, -3851
	ori %r7, %r7, 3846
	stw %r7, 6224(%r6)
	lis %r7, 2990
	ori %r7, %r7, 56622
	stw %r7, 6228(%r6)
	lis %r7, -29708
	ori %r7, %r7, 31205
	stw %r7, 6232(%r6)
	lis %r7, -5805
	ori %r7, %r7, 23917
	stw %r7, 6236(%r6)
	lis %r7, 21358
	ori %r7, %r7, 20163
	stw %r7, 6240(%r6)
	lis %r7, -25630
	ori %r7, %r7, 5486
	stw %r7, 6244(%r6)
	lis %r7, 25972
	ori %r7, %r7, 7643
	stw %r7, 6248(%r6)
	lis %r7, -24617
	ori %r7, %r7, 13873
	stw %r7, 6252(%r6)
	lis %r7, -26486
	ori %r7, %r7, 63253
	stw %r7, 6256(%r6)
	lis %r7, -32029
	ori %r7, %r7, 15837
	stw %r7, 6260(%r6)
	lis %r7, 531
	ori %r7, %r7, 55463
	stw %r7, 6264(%r6)
	lis %r7, 16916
	ori %r7, %r7, 59024
	stw %r7, 6268(%r6)
	lis %r7, -23960
	ori %r7, %r7, 21600
	stw %r7, 6272(%r6)
	lis %r7, -10898
	ori %r7, %r7, 2052
	stw %r7, 6276(%r6)
	lis %r7, -6870
	ori %r7, %r7, 19508
	stw %r7, 6280(%r6)
	lis %r7, -14949
	ori %r7, %r7, 34032
	stw %r7, 6284(%r6)
	lis %r7, -3513
	ori %r7, %r7, 10713
	stw %r7, 6288(%r6)
	lis %r7, 10066
	ori %r7, %r7, 23877
	stw %r7, 6292(%r6)
	lis %r7, -21592
	ori %r7, %r7, 28963
	stw %r7, 6296(%r6)
	lis %r7, 13787
	ori %r7, %r7, 22376
	stw %r7, 6300(%r6)
	lis %r7, 24131
	ori %r7, %r7, 46128
	stw %r7, 6304(%r6)
	lis %r7, 10223
	ori %r7, %r7, 8610
	stw %r7, 6308(%r6)
	lis %r7, 5537
	ori %r7, %r7, 61065
	stw %r7, 6312(%r6)
	lis %r7, 5637
	ori %r7, %r7, 24850
	stw %r7, 6316(%r6)
	lis %r7, -1625
	ori %r7, %r7, 34258
	stw %r7, 6320(%r6)
	lis %r7, -1027
	ori %r7, %r7, 20618
	stw %r7, 6324(%r6)
	lis %r7, -22167
	ori %r7, %r7, 17890
	stw %r7, 6328(%r6)
	lis %r7, -2271
	ori %r7, %r7, 41851
	stw %r7, 6332(%r6)
	lis %r7, 5848
	ori %r7, %r7, 54198
	stw %r7, 6336(%r6)
	lis %r7, 12502
	ori %r7, %r7, 55490
	stw %r7, 6340(%r6)
	lis %r7, -31456
	ori %r7, %r7, 29891
	stw %r7, 6344(%r6)
	lis %r7, 20016
	ori %r7, %r7, 26080
	stw %r7, 6348(%r6)
	lis %r7, -19294
	ori %r7, %r7, 41064
	stw %r7, 6352(%r6)
	lis %r7, -1707
	ori %r7, %r7, 64064
	stw %r7, 6356(%r6)
	lis %r7, 4901
	ori %r7, %r7, 42851
	stw %r7, 6360(%r6)
	lis %r7, -3495
	ori %r7, %r7, 133
	stw %r7, 6364(%r6)
	lis %r7, -11025
	ori %r7, %r7, 6601
	stw %r7, 6368(%r6)
	lis %r7, -24730
	ori %r7, %r7, 22358
	stw %r7, 6372(%r6)
	lis %r7, -28551
	ori %r7, %r7, 40070
	stw %r7, 6376(%r6)
	lis %r7, 8739
	ori %r7, %r7, 12585
	stw %r7, 6380(%r6)
	lis %r7, -18430
	ori %r7, %r7, 31493
	stw %r7, 6384(%r6)
	lis %r7, -31038
	ori %r7, %r7, 45709
	stw %r7, 6388(%r6)
	lis %r7, -29986
	ori %r7, %r7, 2761
	stw %r7, 6392(%r6)
	lis %r7, -2929
	ori %r7, %r7, 47346
	stw %r7, 6396(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 56(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 60(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 64(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 68(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 72(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 76(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 80(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 84(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 88(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 92(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 96(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 100(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 104(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 108(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 0(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 4(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 8(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 12(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 16(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 20(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 24(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 28(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 32(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 36(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 40(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 44(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 48(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 52(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 112(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 116(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 120(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 124(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 128(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 132(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 136(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 140(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 144(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 148(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 152(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 156(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 160(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 164(%r6)
	li %r14, 464
238:
	addi %r14, %r14, -1
	bl {vg_ed448_r32_double}
	rldicr %r9, %r14, 2, 61
	add %r9, %r6, %r9
	lbz %r10, 1066(%r9)
	cmpldi %cr0, %r10, 0
	bne %cr0, 239f
	b 240f
239:
	rldicl %r8, %r10, 57, 7
	li %r12, 0
	subf %r12, %r8, %r12
	xor %r10, %r10, %r12
	subf %r10, %r12, %r10
	li %r8, 255
	and %r10, %r10, %r8
	rldicl %r10, %r10, 63, 1
	rldicr %r9, %r10, 7, 56
	rldicr %r8, %r10, 4, 59
	subf %r9, %r8, %r9
	add %r9, %r9, %r6
	ld %r7, 5504(%r9)
	std %r7, 168(%r6)
	ld %r7, 5512(%r9)
	std %r7, 176(%r6)
	ld %r7, 5520(%r9)
	std %r7, 184(%r6)
	ld %r7, 5528(%r9)
	std %r7, 192(%r6)
	ld %r7, 5536(%r9)
	std %r7, 200(%r6)
	ld %r7, 5544(%r9)
	std %r7, 208(%r6)
	ld %r7, 5552(%r9)
	std %r7, 216(%r6)
	ld %r7, 5560(%r9)
	std %r7, 224(%r6)
	ld %r7, 5568(%r9)
	std %r7, 232(%r6)
	ld %r7, 5576(%r9)
	std %r7, 240(%r6)
	ld %r7, 5584(%r9)
	std %r7, 248(%r6)
	ld %r7, 5592(%r9)
	std %r7, 256(%r6)
	ld %r7, 5600(%r9)
	std %r7, 264(%r6)
	ld %r7, 5608(%r9)
	std %r7, 272(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 241f
	b 242f
241:
	ld %r7, 168(%r6)
	ld %r8, 168(%r6)
	subfc %r7, %r8, %r7
	std %r7, 280(%r6)
	ld %r7, 176(%r6)
	ld %r8, 176(%r6)
	subfe %r7, %r8, %r7
	std %r7, 288(%r6)
	ld %r7, 184(%r6)
	ld %r8, 184(%r6)
	subfe %r7, %r8, %r7
	std %r7, 296(%r6)
	ld %r7, 192(%r6)
	ld %r8, 192(%r6)
	subfe %r7, %r8, %r7
	std %r7, 304(%r6)
	ld %r7, 200(%r6)
	ld %r8, 200(%r6)
	subfe %r7, %r8, %r7
	std %r7, 312(%r6)
	ld %r7, 208(%r6)
	ld %r8, 208(%r6)
	subfe %r7, %r8, %r7
	std %r7, 320(%r6)
	ld %r7, 216(%r6)
	ld %r8, 216(%r6)
	subfe %r7, %r8, %r7
	std %r7, 328(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 280(%r6)
	subfc %r7, %r4, %r7
	std %r7, 280(%r6)
	ld %r7, 288(%r6)
	subfe %r7, %r8, %r7
	std %r7, 288(%r6)
	ld %r7, 296(%r6)
	subfe %r7, %r8, %r7
	std %r7, 296(%r6)
	ld %r7, 304(%r6)
	subfe %r7, %r5, %r7
	std %r7, 304(%r6)
	ld %r7, 312(%r6)
	subfe %r7, %r8, %r7
	std %r7, 312(%r6)
	ld %r7, 320(%r6)
	subfe %r7, %r8, %r7
	std %r7, 320(%r6)
	ld %r7, 328(%r6)
	subfe %r7, %r8, %r7
	std %r7, 328(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 280(%r6)
	subfc %r7, %r4, %r7
	std %r7, 280(%r6)
	ld %r7, 288(%r6)
	subfe %r7, %r8, %r7
	std %r7, 288(%r6)
	ld %r7, 296(%r6)
	subfe %r7, %r8, %r7
	std %r7, 296(%r6)
	ld %r7, 304(%r6)
	subfe %r7, %r5, %r7
	std %r7, 304(%r6)
	ld %r7, 312(%r6)
	subfe %r7, %r8, %r7
	std %r7, 312(%r6)
	ld %r7, 320(%r6)
	subfe %r7, %r8, %r7
	std %r7, 320(%r6)
	ld %r7, 328(%r6)
	subfe %r7, %r8, %r7
	std %r7, 328(%r6)
	ld %r7, 280(%r6)
	ld %r8, 168(%r6)
	subfc %r7, %r8, %r7
	std %r7, 168(%r6)
	ld %r7, 288(%r6)
	ld %r8, 176(%r6)
	subfe %r7, %r8, %r7
	std %r7, 176(%r6)
	ld %r7, 296(%r6)
	ld %r8, 184(%r6)
	subfe %r7, %r8, %r7
	std %r7, 184(%r6)
	ld %r7, 304(%r6)
	ld %r8, 192(%r6)
	subfe %r7, %r8, %r7
	std %r7, 192(%r6)
	ld %r7, 312(%r6)
	ld %r8, 200(%r6)
	subfe %r7, %r8, %r7
	std %r7, 200(%r6)
	ld %r7, 320(%r6)
	ld %r8, 208(%r6)
	subfe %r7, %r8, %r7
	std %r7, 208(%r6)
	ld %r7, 328(%r6)
	ld %r8, 216(%r6)
	subfe %r7, %r8, %r7
	std %r7, 216(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 168(%r6)
	subfc %r7, %r4, %r7
	std %r7, 168(%r6)
	ld %r7, 176(%r6)
	subfe %r7, %r8, %r7
	std %r7, 176(%r6)
	ld %r7, 184(%r6)
	subfe %r7, %r8, %r7
	std %r7, 184(%r6)
	ld %r7, 192(%r6)
	subfe %r7, %r5, %r7
	std %r7, 192(%r6)
	ld %r7, 200(%r6)
	subfe %r7, %r8, %r7
	std %r7, 200(%r6)
	ld %r7, 208(%r6)
	subfe %r7, %r8, %r7
	std %r7, 208(%r6)
	ld %r7, 216(%r6)
	subfe %r7, %r8, %r7
	std %r7, 216(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 168(%r6)
	subfc %r7, %r4, %r7
	std %r7, 168(%r6)
	ld %r7, 176(%r6)
	subfe %r7, %r8, %r7
	std %r7, 176(%r6)
	ld %r7, 184(%r6)
	subfe %r7, %r8, %r7
	std %r7, 184(%r6)
	ld %r7, 192(%r6)
	subfe %r7, %r5, %r7
	std %r7, 192(%r6)
	ld %r7, 200(%r6)
	subfe %r7, %r8, %r7
	std %r7, 200(%r6)
	ld %r7, 208(%r6)
	subfe %r7, %r8, %r7
	std %r7, 208(%r6)
	ld %r7, 216(%r6)
	subfe %r7, %r8, %r7
	std %r7, 216(%r6)
242:
	bl {vg_ed448_r32_add_affine}
240:
	rldicr %r9, %r14, 2, 61
	add %r9, %r6, %r9
	lbz %r10, 1067(%r9)
	cmpldi %cr0, %r10, 0
	bne %cr0, 243f
	b 244f
243:
	rldicl %r8, %r10, 57, 7
	li %r12, 0
	subf %r12, %r8, %r12
	xor %r10, %r10, %r12
	subf %r10, %r12, %r10
	li %r8, 255
	and %r10, %r10, %r8
	rldicl %r10, %r10, 63, 1
	rldicr %r9, %r10, 7, 56
	rldicr %r8, %r10, 5, 58
	add %r9, %r9, %r8
	rldicr %r8, %r10, 3, 60
	add %r9, %r9, %r8
	add %r9, %r9, %r6
	ld %r7, 4160(%r9)
	std %r7, 168(%r6)
	ld %r7, 4168(%r9)
	std %r7, 176(%r6)
	ld %r7, 4176(%r9)
	std %r7, 184(%r6)
	ld %r7, 4184(%r9)
	std %r7, 192(%r6)
	ld %r7, 4192(%r9)
	std %r7, 200(%r6)
	ld %r7, 4200(%r9)
	std %r7, 208(%r6)
	ld %r7, 4208(%r9)
	std %r7, 216(%r6)
	ld %r7, 4216(%r9)
	std %r7, 224(%r6)
	ld %r7, 4224(%r9)
	std %r7, 232(%r6)
	ld %r7, 4232(%r9)
	std %r7, 240(%r6)
	ld %r7, 4240(%r9)
	std %r7, 248(%r6)
	ld %r7, 4248(%r9)
	std %r7, 256(%r6)
	ld %r7, 4256(%r9)
	std %r7, 264(%r6)
	ld %r7, 4264(%r9)
	std %r7, 272(%r6)
	ld %r7, 4272(%r9)
	std %r7, 280(%r6)
	ld %r7, 4280(%r9)
	std %r7, 288(%r6)
	ld %r7, 4288(%r9)
	std %r7, 296(%r6)
	ld %r7, 4296(%r9)
	std %r7, 304(%r6)
	ld %r7, 4304(%r9)
	std %r7, 312(%r6)
	ld %r7, 4312(%r9)
	std %r7, 320(%r6)
	ld %r7, 4320(%r9)
	std %r7, 328(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 245f
	b 246f
245:
	ld %r7, 168(%r6)
	ld %r8, 168(%r6)
	subfc %r7, %r8, %r7
	std %r7, 560(%r6)
	ld %r7, 176(%r6)
	ld %r8, 176(%r6)
	subfe %r7, %r8, %r7
	std %r7, 568(%r6)
	ld %r7, 184(%r6)
	ld %r8, 184(%r6)
	subfe %r7, %r8, %r7
	std %r7, 576(%r6)
	ld %r7, 192(%r6)
	ld %r8, 192(%r6)
	subfe %r7, %r8, %r7
	std %r7, 584(%r6)
	ld %r7, 200(%r6)
	ld %r8, 200(%r6)
	subfe %r7, %r8, %r7
	std %r7, 592(%r6)
	ld %r7, 208(%r6)
	ld %r8, 208(%r6)
	subfe %r7, %r8, %r7
	std %r7, 600(%r6)
	ld %r7, 216(%r6)
	ld %r8, 216(%r6)
	subfe %r7, %r8, %r7
	std %r7, 608(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 560(%r6)
	subfc %r7, %r4, %r7
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	subfe %r7, %r8, %r7
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	subfe %r7, %r8, %r7
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	subfe %r7, %r5, %r7
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	subfe %r7, %r8, %r7
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	subfe %r7, %r8, %r7
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	subfe %r7, %r8, %r7
	std %r7, 608(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 560(%r6)
	subfc %r7, %r4, %r7
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	subfe %r7, %r8, %r7
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	subfe %r7, %r8, %r7
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	subfe %r7, %r5, %r7
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	subfe %r7, %r8, %r7
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	subfe %r7, %r8, %r7
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	subfe %r7, %r8, %r7
	std %r7, 608(%r6)
	ld %r7, 560(%r6)
	ld %r8, 168(%r6)
	subfc %r7, %r8, %r7
	std %r7, 168(%r6)
	ld %r7, 568(%r6)
	ld %r8, 176(%r6)
	subfe %r7, %r8, %r7
	std %r7, 176(%r6)
	ld %r7, 576(%r6)
	ld %r8, 184(%r6)
	subfe %r7, %r8, %r7
	std %r7, 184(%r6)
	ld %r7, 584(%r6)
	ld %r8, 192(%r6)
	subfe %r7, %r8, %r7
	std %r7, 192(%r6)
	ld %r7, 592(%r6)
	ld %r8, 200(%r6)
	subfe %r7, %r8, %r7
	std %r7, 200(%r6)
	ld %r7, 600(%r6)
	ld %r8, 208(%r6)
	subfe %r7, %r8, %r7
	std %r7, 208(%r6)
	ld %r7, 608(%r6)
	ld %r8, 216(%r6)
	subfe %r7, %r8, %r7
	std %r7, 216(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 168(%r6)
	subfc %r7, %r4, %r7
	std %r7, 168(%r6)
	ld %r7, 176(%r6)
	subfe %r7, %r8, %r7
	std %r7, 176(%r6)
	ld %r7, 184(%r6)
	subfe %r7, %r8, %r7
	std %r7, 184(%r6)
	ld %r7, 192(%r6)
	subfe %r7, %r5, %r7
	std %r7, 192(%r6)
	ld %r7, 200(%r6)
	subfe %r7, %r8, %r7
	std %r7, 200(%r6)
	ld %r7, 208(%r6)
	subfe %r7, %r8, %r7
	std %r7, 208(%r6)
	ld %r7, 216(%r6)
	subfe %r7, %r8, %r7
	std %r7, 216(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 168(%r6)
	subfc %r7, %r4, %r7
	std %r7, 168(%r6)
	ld %r7, 176(%r6)
	subfe %r7, %r8, %r7
	std %r7, 176(%r6)
	ld %r7, 184(%r6)
	subfe %r7, %r8, %r7
	std %r7, 184(%r6)
	ld %r7, 192(%r6)
	subfe %r7, %r5, %r7
	std %r7, 192(%r6)
	ld %r7, 200(%r6)
	subfe %r7, %r8, %r7
	std %r7, 200(%r6)
	ld %r7, 208(%r6)
	subfe %r7, %r8, %r7
	std %r7, 208(%r6)
	ld %r7, 216(%r6)
	subfe %r7, %r8, %r7
	std %r7, 216(%r6)
246:
	bl {vg_ed448_r32_add}
	ld %r7, 392(%r6)
	std %r7, 56(%r6)
	ld %r7, 400(%r6)
	std %r7, 64(%r6)
	ld %r7, 408(%r6)
	std %r7, 72(%r6)
	ld %r7, 416(%r6)
	std %r7, 80(%r6)
	ld %r7, 424(%r6)
	std %r7, 88(%r6)
	ld %r7, 432(%r6)
	std %r7, 96(%r6)
	ld %r7, 440(%r6)
	std %r7, 104(%r6)
	ld %r7, 448(%r6)
	std %r7, 0(%r6)
	ld %r7, 456(%r6)
	std %r7, 8(%r6)
	ld %r7, 464(%r6)
	std %r7, 16(%r6)
	ld %r7, 472(%r6)
	std %r7, 24(%r6)
	ld %r7, 480(%r6)
	std %r7, 32(%r6)
	ld %r7, 488(%r6)
	std %r7, 40(%r6)
	ld %r7, 496(%r6)
	std %r7, 48(%r6)
	ld %r7, 504(%r6)
	std %r7, 112(%r6)
	ld %r7, 512(%r6)
	std %r7, 120(%r6)
	ld %r7, 520(%r6)
	std %r7, 128(%r6)
	ld %r7, 528(%r6)
	std %r7, 136(%r6)
	ld %r7, 536(%r6)
	std %r7, 144(%r6)
	ld %r7, 544(%r6)
	std %r7, 152(%r6)
	ld %r7, 552(%r6)
	std %r7, 160(%r6)
244:
	cmpldi %cr0, %r14, 0
	bne %cr0, 238b
	ld %r7, 3120(%r6)
	std %r7, 168(%r6)
	ld %r7, 3128(%r6)
	std %r7, 176(%r6)
	ld %r7, 3136(%r6)
	std %r7, 184(%r6)
	ld %r7, 3144(%r6)
	std %r7, 192(%r6)
	ld %r7, 3152(%r6)
	std %r7, 200(%r6)
	ld %r7, 3160(%r6)
	std %r7, 208(%r6)
	ld %r7, 3168(%r6)
	std %r7, 216(%r6)
	ld %r7, 3176(%r6)
	std %r7, 224(%r6)
	ld %r7, 3184(%r6)
	std %r7, 232(%r6)
	ld %r7, 3192(%r6)
	std %r7, 240(%r6)
	ld %r7, 3200(%r6)
	std %r7, 248(%r6)
	ld %r7, 3208(%r6)
	std %r7, 256(%r6)
	ld %r7, 3216(%r6)
	std %r7, 264(%r6)
	ld %r7, 3224(%r6)
	std %r7, 272(%r6)
	bl {vg_ed448_r32_add_affine}
	bl {vg_ed448_r32_double}
	bl {vg_ed448_r32_double}
	ld %r7, 3536(%r6)
	mtlr %r7
	ld %r14, 3544(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	or %r10, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r10
	std %r9, 3520(%r6)
	ld %r7, 0(%r6)
	ld %r8, 112(%r6)
	subfc %r7, %r8, %r7
	std %r7, 560(%r6)
	ld %r7, 8(%r6)
	ld %r8, 120(%r6)
	subfe %r7, %r8, %r7
	std %r7, 568(%r6)
	ld %r7, 16(%r6)
	ld %r8, 128(%r6)
	subfe %r7, %r8, %r7
	std %r7, 576(%r6)
	ld %r7, 24(%r6)
	ld %r8, 136(%r6)
	subfe %r7, %r8, %r7
	std %r7, 584(%r6)
	ld %r7, 32(%r6)
	ld %r8, 144(%r6)
	subfe %r7, %r8, %r7
	std %r7, 592(%r6)
	ld %r7, 40(%r6)
	ld %r8, 152(%r6)
	subfe %r7, %r8, %r7
	std %r7, 600(%r6)
	ld %r7, 48(%r6)
	ld %r8, 160(%r6)
	subfe %r7, %r8, %r7
	std %r7, 608(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 560(%r6)
	subfc %r7, %r4, %r7
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	subfe %r7, %r8, %r7
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	subfe %r7, %r8, %r7
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	subfe %r7, %r5, %r7
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	subfe %r7, %r8, %r7
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	subfe %r7, %r8, %r7
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	subfe %r7, %r8, %r7
	std %r7, 608(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 560(%r6)
	subfc %r7, %r4, %r7
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	subfe %r7, %r8, %r7
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	subfe %r7, %r8, %r7
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	subfe %r7, %r5, %r7
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	subfe %r7, %r8, %r7
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	subfe %r7, %r8, %r7
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	subfe %r7, %r8, %r7
	std %r7, 608(%r6)
	li %r11, 0
	lwz %r5, 560(%r6)
	lwz %r7, 560(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 56(%r6)
	lwz %r5, 564(%r6)
	lwz %r7, 564(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 60(%r6)
	lwz %r5, 568(%r6)
	lwz %r7, 568(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 64(%r6)
	lwz %r5, 572(%r6)
	lwz %r7, 572(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 68(%r6)
	lwz %r5, 576(%r6)
	lwz %r7, 576(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 72(%r6)
	lwz %r5, 580(%r6)
	lwz %r7, 580(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 76(%r6)
	lwz %r5, 584(%r6)
	lwz %r7, 584(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 80(%r6)
	lwz %r5, 588(%r6)
	lwz %r7, 588(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 84(%r6)
	lwz %r5, 592(%r6)
	lwz %r7, 592(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 88(%r6)
	lwz %r5, 596(%r6)
	lwz %r7, 596(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 92(%r6)
	lwz %r5, 600(%r6)
	lwz %r7, 600(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 96(%r6)
	lwz %r5, 604(%r6)
	lwz %r7, 604(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 100(%r6)
	lwz %r5, 608(%r6)
	lwz %r7, 608(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 104(%r6)
	lwz %r5, 612(%r6)
	lwz %r7, 612(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 108(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	or %r10, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r10
	std %r9, 3520(%r6)
	ld %r9, 3520(%r6)
	li %r8, 0
	subf %r8, %r9, %r8
	or %r9, %r9, %r8
	rldicl %r9, %r9, 1, 63
	li %r3, 1
	subf %r3, %r9, %r3
	blr
