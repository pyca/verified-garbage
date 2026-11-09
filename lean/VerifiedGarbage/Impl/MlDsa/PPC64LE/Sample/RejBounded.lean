module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.Common

/-!
# ML-DSA on PPC64LE: `vg_mldsa_rej_bounded_poly`

`rejBounded(seed = r3, eta = r4, a = r5, scratch = r6) -> r3` (see
`Common.lean` for the layout) squeezes 272 bytes of SHAKE256 of the 66
bytes of the seed (2 blocks), which the first 272 iterations of
`RejBoundedPoly`'s loop take a byte at a time (`rbTry 272`); in the rare case
that fewer than 256 coefficients are accepted, it starts again with 544 bytes
(`rbTry 544`, 4 blocks; the least bound of FIPS 204 Appendix C is 481 bytes),
which the 544 iterations of the loop take, as on 32-bit ARM. Starting again
squeezes the first 272 bytes again, but keeps the code that continues a
squeeze out of the function, and is all but never taken: 544 half-bytes have
fewer than 256 accepted with probability below 2⁻¹⁶ for `η = 4`, and far
less for `η = 2`. The loop (`rbLoop η n`, one for each `η`, chosen by a
branch on the public `η`) runs with `r3` at the byte of the iteration,
`r4` at `a[j]`, `r5` = `j`, the number of coefficients sampled, `r6`
counting down and `r7` = `q`: each half-byte `b` of the byte (low first, in
`r9`) that `CoeffFromHalfByte` accepts (`b < 15` for `η = 2`, `b < 9` for
`η = 4`), while `j < 256`, gives the coefficient `η - (b mod 5)` or `η - b`,
stored modulo `q` to `a[j]` (and `j` incremented). It returns `j >> 8`: 1 if
`j = 256`, and 0 otherwise.

The coefficient is computed without a branch or a table (`rbVal`), before
the test: `b mod 5` by subtracting 10 and then 5, each added back if the
result is negative (from its sign bit), and `q` added to `η - (b mod 5)` if
it is negative. So the loop's branches and the addresses of its stores depend
only on which half-bytes are accepted (and `j`, which counts them), which the
contract lets it leak, not on the coefficients.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Sample

open VG.PPC64LE
open VG.Impl.Sha3.PPC64LE.Stream (mov)

/-- `r9 ← r9 - s`, plus `s` if that is negative, for `s` 10 or 5, through
`r10` and `r11`. -/
def csub (s : Nat) : List Instr :=
  ([.subi .r9 .r9 s, .lsr .d .r11 .r9 63] : List Instr) ++
    (if s = 10 then [.lsl .r10 .r11 3, .add .r9 .r9 .r10, .lsl .r10 .r11 1, .add .r9 .r9 .r10]
      else [.lsl .r10 .r11 2, .add .r9 .r9 .r10, .add .r9 .r9 .r11])

/-- The coefficient of the half-byte `r9`, modulo `q`, in `r10`: `η - (b mod 5)`
for `η = 2`, `η - b` for `η = 4`. -/
def rbVal : Nat → List Instr
  | 2 => csub 10 ++ csub 5 ++ ([.li .r10 2, .sub .r10 .r10 .r9] : List Instr) ++ addQNeg .r10
  | _ => ([.li .r10 4, .sub .r10 .r10 .r9] : List Instr) ++ addQNeg .r10

/-- The half-bytes `CoeffFromHalfByte` accepts: those less than this. -/
def rbBound : Nat → Nat
  | 2 => 15
  | _ => 9

/-- The half-byte `r9`: its coefficient in `r10`, and `r12 ≠ 0` iff it is
accepted and `j < 256`. -/
def rbHalf (η : Nat) : List Instr := testJ [.subi .r12 .r9 (rbBound η)] ++ rbVal η

def rbBody (η : Nat) : Prog isa :=
  .seq (.block ([.lbz .r8 .r3 0, .lsl .r9 .r8 60, .lsr .d .r9 .r9 60] ++ rbHalf η))
    (.seq (accept .r10)
      (.seq (.block (.lsr .d .r9 .r8 4 :: rbHalf η))
        (.seq (accept .r10) (.block [.addi .r3 .r3 1, .subi .r6 .r6 1]))))

/-- The loop over `n` bytes, from the XOF output at `scratch + 840`. -/
def rbLoop (η n : Nat) : Prog isa :=
  .seq (.block ([.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 n] ++ loadQ))
    (.loop (rbBody η) (.nonzero .d .r6))

/-- `n` bytes squeezed, and the loop over them for `η`. -/
def rbTry (n : Nat) : Prog isa :=
  .seq (sponge 136 n) (.seq (.block [.subi .r12 .r27 2]) (.ite (.zero .d .r12) (rbLoop 2 n) (rbLoop 4 n)))

def rejBounded : Prog isa :=
  .seq (.block (pro .r6 .r5 .r3 [.li .r28 66] (zext32 .r27 .r4)))
    (.seq (rbTry 272)
      (.seq (.seq (.block [.subi .r12 .r5 256]) (.ite (.zero .d .r12) (.block []) (rbTry 544)))
        (.block (retJ ++ epi))))

end VG.Impl.MlDsa.PPC64LE.Sample
