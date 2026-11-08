module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.Div

/-!
# A division with a short divisor, in the RSA key operations' working space

`div q r d t v`: the `32 w` steps of `Impl/Rsa/PPC64LE/Div.lean`'s division
of the dividend in array `q` (`w` digits) by a divisor in array `d` below
`2^(32 v)`, for `v < w`. The quotient is shifted over its `w` digits as
there, but the remainder, which stays below the divisor, is shifted,
subtracted from and selected over its first `v + 1` digits only, by digit
loops of `v + 1` steps. The remainder's digits from `v + 1` to `w − 1` are
zeroed at the end, so that array `r` holds the remainder as a number of `w`
digits.

The counts are `w` (`r29`) and the constant `v`, so the addresses and
branches depend only on `w`, `v` and the base.
-/

@[expose] public section

namespace VG.Impl.Dsa.PPC64LE.DivN

open VG.PPC64LE VG.Impl.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Div (shlBody shlWBody bit setBit init)

/-- The quotient shifted left over its `w` digits, its top bit out in `r9`. -/
def shiftQ (q : Nat) : Prog isa :=
  .seq (.block (ptr .r5 q ++ [.li .r9 0]))
    (evenW (.seq (.block [.lsr .d .r8 .r29 1]) (countLoop .r8 shlWBody))
      (.seq (.block [.addi .r8 .r29 0]) (countLoop .r8 shlBody)))

/-- The remainder's `v + 1` digits shifted left, `r9` in. -/
def shiftR (r v : Nat) : Prog isa :=
  .seq (.block (ptr .r5 r)) (.seq (.block [.li .r8 (v + 1)]) (countLoop .r8 shlBody))

/-- `[t] := [r] - [d]` over `v + 1` digits, the borrow in `r9`. -/
def subtract (r d t v : Nat) : Prog isa :=
  .seq (.block (ptr .r5 t ++ ptr .r6 r ++ ptr .r7 d))
    (.seq (.block [.li .r8 (v + 1), .li .r9 0]) (countLoop .r8 subBody))

/-- `[r] := mask ? [t] : [r]` over `v + 1` digits. -/
def keep (r t v : Nat) : Prog isa :=
  .seq (.block (ptr .r5 r ++ ptr .r6 r ++ ptr .r7 t))
    (.seq (.block [.li .r8 (v + 1)]) (countLoop .r8 selBody))

/-- The quotient and the remainder shifted left together. -/
def shift (q r v : Nat) : Prog isa := .seq (shiftQ q) (shiftR r v)

/-- One step. -/
def step (q r d t v : Nat) : Prog isa :=
  .seq (shift q r v) (.seq (subtract r d t v) (.seq (.block bit) (.seq (keep r t v) (.block (setBit q)))))

/-- The remainder's digits `v + 1` to `w − 1` zeroed. -/
def zeroHi (r v : Nat) : Prog isa :=
  .seq (.block (ptr .r5 r ++ [.addi .r5 .r5 (4 * (v + 1)), .subi .r8 .r29 (v + 1), .li .r0 0]))
    (countLoop .r8 [.store .w .r0 .r5 0, .addi .r5 .r5 4])

/-- `32 w` division steps of `[q]` by `[d] < 2^(32 v)`: the quotient in `[q]`
and the remainder in `[r]`. -/
def div (q r d t v : Nat) : Prog isa :=
  .seq (init r) (.seq (.loop (step q r d t v) (.nonzero .d .r4)) (zeroHi r v))

end VG.Impl.Dsa.PPC64LE.DivN
