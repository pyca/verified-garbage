module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute

/-!
# The RSA public-key operation on PPC64LE

`vg_rsa_public_precomputed_checked(out = r3, out_len = r4, pre = r5,
pre_len = r6, e = r7, e_len = r8, input = r9, input_len = r10, scratch,
scratch_len)`, `scratch` and `scratch_len` on the stack: with `pre` holding
`n` and `R² mod n` of a modulus of `k = out_len` bytes and `w = ⌈k / 8⌉`
words, writes `input^e mod n` (`k` bytes, most significant first) to `out`
and returns 1, or writes zeros and returns 0 if `e` is not odd and from 3 to
`2^33 - 1` or the input is not below `n`.

Nothing branches on a value read from memory: the code is the same for every
`e` and input of the same lengths. `e` is read into `r24`, saturated at
`2^33`; its 33 bits are scanned from the top, each step a Montgomery square
and a Montgomery multiplication by the input, the product selected with a
mask of the bit. The Montgomery multiplications are `MontMul.lean`'s `tail`,
inline, in its working space (`n` in array 0, `R² mod n` in array 1, its
accumulator and temporary in arrays 2 and 3, the input and the product in
array 4, the power in array 5, `x R mod n` in array 6, 1 in array 7). The
result is written with a mask of whether `e` and the input are valid.

Registers kept throughout: `r23` the working space, `r24` the exponent's
bits, `r25` the bits left, `r26` the validity mask, `r27` `out`, `r28` `k`,
`r29` an array's size in bytes, `r10` array 0's base, `r11` `2 w`, `r12`
`-n⁻¹ mod 2³²`. The nonvolatile registers are saved in the header's words
16–31.
-/

@[expose] public section

namespace VG.Impl.Bignum.PPC64LE.PublicChecked

open VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE

/-- The nonvolatile registers saved, `r23` (the working space) last. -/
def saved (i : Nat) : Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r24, .r25, .r26, .r27, .r28, .r29, .r23].getD i
    .r14

/-- The working space from the stack into `r11`, the registers saved there,
and its address into `r23`. -/
def save : List Instr :=
  [.addSp .r11 96, .load .d .r11 .r11 0] ++
    (List.range 16).flatMap (fun i => [.store .d (saved i) .r11 (128 + 8 * i)]) ++ [.addi .r23 .r11 0]

/-- The registers back, through `r23`, which is restored last. -/
def restore : List Instr :=
  (List.range 15).flatMap (fun i => [.load .d (saved i) .r23 (128 + 8 * i)]) ++
    [.load .d .r23 .r23 (128 + 8 * 15)]

/-- `out` and `k` kept, `w`, the arrays' size, array 0's base and `2 w`. -/
def setup : List Instr :=
  [.addi .r27 .r3 0, .addi .r28 .r4 0, .addi .r11 .r4 7, .lsr .d .r11 .r11 3, .lsl .r29 .r11 3,
    .addi .r29 .r29 16, .addi .r10 .r23 hdrBytes, .lsl .r11 .r11 1]

/-- `e`'s `e_len` bytes (`r7`, `r8`) into `r24`, as a number saturated at
`2^33`: after each byte, `r24 := 2^33` if it is at least that. -/
def readE : Prog isa :=
  .seq (.block [.li .r24 0])
    (Precompute.countLoop .r8 [.lbz .r0 .r7 0, .lsl .r24 .r24 8, .logic .or .r24 .r24 .r0,
      .lsr .d .r3 .r24 33, .li .r4 0, .sub .r3 .r4 .r3, .lsr .d .r3 .r3 63, .sub .r3 .r4 .r3,
      .li .r4 1, .lsl .r4 .r4 33, .logic .xor .r0 .r24 .r4, .logic .and .r0 .r0 .r3,
      .logic .xor .r24 .r24 .r0, .addi .r7 .r7 1])

/-- `r26 :=` all ones if `r24` is odd, at least 3 and below `2^33`, else 0;
then `r24`'s bit 32 to the top. -/
def checkE : List Instr :=
  [.li .r4 1, .logic .and .r0 .r24 .r4, .subi .r3 .r24 3, .lsr .d .r3 .r3 63, .logic .xor .r3 .r3 .r4,
    .logic .and .r0 .r0 .r3, .lsl .r3 .r4 33, .sub .r3 .r24 .r3, .lsr .d .r3 .r3 63,
    .logic .and .r0 .r0 .r3, .li .r3 0, .sub .r26 .r3 .r0, .lsl .r24 .r24 31]

/-- `rd :=` the base of array `j`: array 0's plus `j` arrays. -/
def base (rd : Reg) (j : Nat) : List Instr :=
  .addi rd .r10 0 :: List.replicate j (.add rd rd .r29)

/-- `n` (`w` words at `pre`, `r5`) into array 0 and `R² mod n` (the next `w`)
into array 1. -/
def copyPre : Prog isa :=
  .seq (.block [.addi .r14 .r10 0, .addi .r15 .r5 0]) (.seq Precompute.copyWords
    (.seq (.block [.add .r14 .r10 .r29]) Precompute.copyWords))

/-- The input's `k` bytes (`r9`) into array 4, and the array's word `w` := 0. -/
def loadX : Prog isa :=
  .seq (.block (base .r10 4 ++ [.addi .r12 .r9 0, .addi .r6 .r28 0])) (.seq Precompute.loadN
    (.block [.add .r14 .r10 .r29, .subi .r14 .r14 16, .li .r0 0, .store .d .r0 .r14 0,
      .addi .r10 .r23 hdrBytes]))

/-- `r12 := -n⁻¹ mod 2³²`, from `n`'s low word, by Newton's iteration
`x := x (2 - n x)` from `x = n`. -/
def minv : List Instr :=
  [.load .d .r0 .r10 0, .load .d .r12 .r10 0] ++
    (List.range 4).flatMap (fun _ => [.mul .r3 .r0 .r12, .li .r4 2, .sub .r3 .r4 .r3, .mul .r12 .r12 .r3]) ++
    [.li .r3 0, .sub .r12 .r3 .r12, .lsl .r12 .r12 32, .lsr .d .r12 .r12 32]

/-- `r26 &=` all ones if the input (array 4) is below `n`: the mask of
`subMod`, into array 3. -/
def checkX : Prog isa :=
  .seq (.block (base .r8 4 ++ base .r9 3)) (.seq subMod (.block [.logic .and .r26 .r26 .r20]))

/-- `[o] := [a] [b] R⁻¹ mod n`: `tail`, with the bases. -/
def montOp (o a b : Nat) : Prog isa :=
  .seq (.block (base .r5 o ++ base .r6 a ++ base .r7 b ++ base .r8 2 ++ base .r9 3 ++ [.addi .r4 .r11 0]))
    tail

/-- 1 in array 7. -/
def one : Prog isa :=
  .seq (.block (base .r14 7)) (.seq Precompute.zeroWords
    (.block (base .r14 7 ++ [.li .r0 1, .store .w .r0 .r14 0])))

/-- A step of the scan: `a := a²`, then `a := a x` if the top bit of `r24`
is set, by a mask; `r24` shifted left. -/
def step : Prog isa :=
  .seq (montOp 5 5 5) (.seq (montOp 4 5 6)
    (.seq (.block ([.lsr .d .r0 .r24 63, .li .r3 0, .sub .r20 .r3 .r0, .lsl .r24 .r24 1] ++
        base .r8 4 ++ base .r9 5 ++ base .r5 5)) selectAcc))

/-- `x^e mod n` into array 4: `a := R mod n`, `x R mod n` into array 6, the
33 steps, then out of Montgomery form. -/
def power : Prog isa :=
  .seq one (.seq (montOp 5 1 7) (.seq (montOp 6 4 1) (.seq (.block [.li .r25 33])
    (.seq (.loop (.seq step (.block [.subi .r25 .r25 1])) (.nonzero .d .r25)) (montOp 4 5 7)))))

/-- The result's `k` bytes, most significant first, masked by `r26`, to
`out`; `r3 := 1` if valid, else 0. -/
def output : Prog isa :=
  .seq (.block (base .r15 4 ++ [.add .r15 .r15 .r28, .subi .r15 .r15 1, .addi .r16 .r27 0,
      .addi .r17 .r28 0]))
    (.seq (Precompute.countLoop .r17 [.lbz .r0 .r15 0, .logic .and .r0 .r0 .r26, .stb .r0 .r16 0,
        .addi .r16 .r16 1, .subi .r15 .r15 1])
      (.block [.li .r3 1, .logic .and .r3 .r3 .r26]))

/-- `vg_rsa_public_precomputed_checked`. -/
def publicChecked : Prog isa :=
  .seq (.block (save ++ setup)) (.seq readE (.seq (.block checkE) (.seq copyPre (.seq loadX
    (.seq (.block minv) (.seq checkX (.seq power (.seq output (.block restore)))))))))

end VG.Impl.Bignum.PPC64LE.PublicChecked
