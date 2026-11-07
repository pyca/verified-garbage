module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.TComb

/-!
# Short Weierstrass curves on x86-64: the fixed-base comb for any `a`

The comb of `Impl/Weierstrass/X86_64/TComb.lean` (`TCombCfg.comb`), its
additions by the complete formulas for any `a` (`rcb`, Renes, Costello and
Batina's Algorithm 1) rather than those for `a = -3`: for a curve such as
brainpoolP256r1, whose `a` is not `-3`. The entry, selected and negated as
there, is added to `A` with `a R mod p` in `S.a` and `3 b R mod p` in the slot
of `-y` (`neg`), which the negation has finished with, set each iteration
(`b3`, a constant), so that the comb's other slots are those of
`TCombCfg.comb`. As there, `A` takes the sum unless the digit is zero. This is
AArch64's `TCombCfg.generalComb` (`Impl/Weierstrass/AArch64/TCombGeneral.lean`).
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.TCombCfg

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

variable (K : TCombCfg)

/-- The complete addition's slots: `K.S`, with `3 b R mod p` in `neg`. -/
def generalS : RcbSlots := { K.S with b3 := K.neg }

/-- Iteration `j = rbx - 1`: `step`, adding by `rcb` with `3 b R mod p`
(`b3`) put in `neg` first. -/
def generalStep (b3 : Nat) (publicLookup : Bool := false) : Prog isa :=
  .seq (.block ([.alu .sub .rbx (.imm 1)] ++ K.digit ++ (if publicLookup then K.selectPublic else K.select))) <|
  .seq (.block K.negY) <|
  .seq (.block (setConst K.M.n K.neg b3)) <|
  .seq (fprogB K.M (rcb K.generalS K.A K.E K.D)) <|
  .block (K.digit ++ eqMask 0 ++ selPt K.M.n K.A K.D K.A ++ [.alu .test .rbx (.reg .rbx)])

/-- `[k]G` into `A`, by `generalStep`. -/
def generalComb (b3 : Nat) (publicLookup : Bool := false) : Prog isa :=
  .seq (.block K.init) (.loop (K.generalStep b3 publicLookup) .ne)

end VG.Impl.Weierstrass.X86_64.TCombCfg
