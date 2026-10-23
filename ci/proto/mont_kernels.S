@ Throwaway prototype, never part of the library: Montgomery-row kernels
@ for 32-bit Arm, scheduled and register-allocated by hand as the Lean code
@ would be, so that their timings compare designs, not a compiler's register
@ allocation. Each computes the CIOS accumulator t (n + 2 words, zero on
@ entry, n a multiple of 4, n >= 8) of a b R^-1 mod m; C reduces it.
@
@ void k(u32 *t, const struct ctx *c), struct ctx { b, m, minv, n, bm, a }
@ (bm: b and m interleaved, b_0 m_0 b_1 m_1 ...).

        .syntax unified
        .text

#ifdef __thumb__
#define FUNC(name) .global name; .type name, %function; .thumb_func; .align 2; name:
#else
#define FUNC(name) .global name; .type name, %function; .align 2; name:
#endif

@ The outer frame: [sp] a pointer, [sp, #4] rows (passes) left, [sp, #8]
@ ctx, [sp, #12] t.
.macro ENTER rows_shift
        push    {r4-r11, lr}
        sub     sp, sp, #16
        ldr     r2, [r1, #20]
        str     r2, [sp, #0]
        ldr     r2, [r1, #12]
        .if \rows_shift
        lsr     r2, r2, #\rows_shift
        .endif
        str     r2, [sp, #4]
        str     r1, [sp, #8]
        str     r0, [sp, #12]
.endm

.macro LEAVE
        add     sp, sp, #16
        pop     {r4-r11, pc}
.endm

@ The verified Fios.args, first and body (Impl/Bignum/Arm/Fios.lean): r1 the
@ word of a, r2 the quotient, r12 b, r4 m, r0 t, lr the count, r7 and r8
@ the product's and the cancellation's carries.
.macro FIOS_START
        ldr     r9, [sp, #8]
        ldr     r3, [sp, #0]
        ldr     r1, [r3]
        add     r3, r3, #4
        str     r3, [sp, #0]
        ldr     lr, [r9, #12]
        ldr     r12, [r9, #0]
        ldr     r4, [r9, #4]
        ldr     r2, [r9, #8]
        ldr     r0, [sp, #12]
        mov     r7, #0
        mov     r8, #0
        @ first
        ldr     r3, [r12]
        ldr     r5, [r4]
        ldr     r6, [r0]
        umaal   r6, r7, r3, r1
        mul     r2, r2, r6
        umaal   r6, r8, r5, r2
        add     r12, r12, #4
        add     r4, r4, #4
        subs    lr, lr, #1
        @ body
        ldr     r3, [r12]
        ldr     r5, [r4]
        ldr     r6, [r0, #4]
        umaal   r6, r7, r3, r1
        umaal   r6, r8, r5, r2
        str     r6, [r0]
        add     r0, r0, #4
        add     r12, r12, #4
        add     r4, r4, #4
        subs    lr, lr, #1
.endm

@ Fios.top, then the row count.
.macro FIOS_END label
        ldr     r3, [r0, #4]
        ldr     r4, [r0, #8]
        adds    r3, r3, r7
        adc     r4, r4, #0
        adds    r3, r3, r8
        adc     r4, r4, #0
        str     r3, [r0]
        str     r4, [r0, #4]
        ldr     r3, [sp, #4]
        subs    r3, r3, #1
        str     r3, [sp, #4]
        bne     \label
.endm

@ 1. The verified generic kernel: Fios.loop, two words an iteration
@ (pairStep, pairAdvance): 17 instructions for 4 UMAALs.
FUNC(k_fios1)
        ENTER   0
1:      FIOS_START
2:      ldr     r3, [r12]
        ldr     r6, [r0, #4]
        umaal   r6, r7, r3, r1
        ldr     r3, [r12, #4]
        ldr     r10, [r0, #8]
        umaal   r10, r7, r3, r1
        ldr     r5, [r4]
        umaal   r6, r8, r5, r2
        str     r6, [r0]
        ldr     r5, [r4, #4]
        umaal   r10, r8, r5, r2
        str     r10, [r0, #4]
        add     r0, r0, #8
        add     r12, r12, #8
        add     r4, r4, #8
        subs    lr, lr, #2
        bne     2b
        FIOS_END 1b
        LEAVE

@ FiosPipelined's steps (Impl/Bignum/Arm/FiosPipelined.lean).
.macro PRODUCT k, dst
        ldr     r3, [r12, #\k]
        ldr     \dst, [r0, #(\k + 4)]
        umaal   \dst, r7, r3, r1
.endm
.macro CANCEL k, dst
        ldr     r5, [r4, #\k]
        umaal   \dst, r8, r5, r2
        str     \dst, [r0, #\k]
.endm
.macro STEP k, pending, next
        PRODUCT (\k + 4), \next
        CANCEL  \k, \pending
.endm
.macro PAIR k
        STEP    \k, r6, r10
        STEP    (\k + 4), r10, r6
.endm

@ 2. The pipelined scan of FiosFast, in a loop over any width: two pairs
@ (four words) an iteration, then FiosPipelined's tail. 29 instructions
@ for 8 UMAALs.
FUNC(k_fios1p)
        ENTER   0
1:      FIOS_START
        PRODUCT 0, r6
        sub     lr, lr, #2
2:      PAIR    0
        PAIR    8
        add     r0, r0, #16
        add     r12, r12, #16
        add     r4, r4, #16
        subs    lr, lr, #4
        bne     2b
        STEP    0, r6, r10
        CANCEL  4, r10
        add     r0, r0, #8
        add     r12, r12, #8
        add     r4, r4, #8
        FIOS_END 1b
        LEAVE

@ 3. Two rows a pass: rows i and i + 1, a0 = r2, q0 = r3, a1 = r4, q1 = r5,
@ carries r6 r7 (row i) and r8 r9 (row i + 1); r0 t, r1 bm, r10 the
@ accumulator word, r11 r12 a word of b and m, lr the count. In each step
@ row i takes word j + 1 (output word j) and row i + 1 word j (output word
@ j - 1): one load and store of t for four UMAALs, on four carry chains.
.macro STEP2 o
        ldr     r10, [r0, #(8 + 4 * \o)]
        ldr     r11, [r1, #(16 + 8 * \o)]
        ldr     r12, [r1, #(20 + 8 * \o)]
        umaal   r10, r6, r11, r2
        umaal   r10, r7, r12, r3
        ldr     r11, [r1, #(8 + 8 * \o)]
        ldr     r12, [r1, #(12 + 8 * \o)]
        umaal   r10, r8, r11, r4
        umaal   r10, r9, r12, r5
        str     r10, [r0, #(4 * \o)]
.endm

FUNC(k_fios2)
        ENTER   1
1:      ldr     r12, [sp, #8]
        ldr     r11, [sp, #0]
        ldr     r2, [r11]
        ldr     r4, [r11, #4]
        add     r11, r11, #8
        str     r11, [sp, #0]
        ldr     r1, [r12, #16]
        ldr     lr, [r12, #12]
        sub     lr, lr, #2
        ldr     r0, [sp, #12]
        mov     r6, #0
        mov     r7, #0
        mov     r8, #0
        mov     r9, #0
        @ row i, word 0: q0
        ldr     r10, [r0]
        ldr     r11, [r1]
        umaal   r10, r6, r11, r2
        ldr     r3, [r12, #8]
        mul     r3, r3, r10
        ldr     r11, [r1, #4]
        umaal   r10, r7, r11, r3
        @ row i, word 1: output word 0
        ldr     r10, [r0, #4]
        ldr     r11, [r1, #8]
        umaal   r10, r6, r11, r2
        ldr     r11, [r1, #12]
        umaal   r10, r7, r11, r3
        @ row i + 1, word 0: q1
        ldr     r11, [r1]
        umaal   r10, r8, r11, r4
        ldr     r5, [r12, #8]
        mul     r5, r5, r10
        ldr     r11, [r1, #4]
        umaal   r10, r9, r11, r5
2:      STEP2   0
        STEP2   1
        add     r0, r0, #8
        add     r1, r1, #16
        subs    lr, lr, #2
        bne     2b
        @ row i's top word (output word n - 1, and n in r11)
        ldr     r10, [r0, #8]
        mov     r11, #0
        adds    r10, r10, r6
        adc     r11, r11, #0
        adds    r10, r10, r7
        adc     r11, r11, #0
        @ row i + 1, word n - 1 (output word n - 2)
        ldr     r12, [r1, #8]
        umaal   r10, r8, r12, r4
        ldr     r12, [r1, #12]
        umaal   r10, r9, r12, r5
        str     r10, [r0]
        @ row i + 1's top word
        adds    r11, r11, r8
        mov     r12, #0
        adc     r12, r12, #0
        adds    r11, r11, r9
        adc     r12, r12, #0
        str     r11, [r0, #4]
        str     r12, [r0, #8]
        ldr     r3, [sp, #4]
        subs    r3, r3, #1
        str     r3, [sp, #4]
        bne     1b
        LEAVE

        .section .note.GNU-stack, "", %progbits
