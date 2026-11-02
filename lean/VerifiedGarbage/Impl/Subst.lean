module

public import VerifiedGarbage.TCB.Code

/-!
# Replacing a piece of code

`Code.subst a b c` is `c` with every occurrence of the code `a` replaced by
`b` (but inside an indirect call, which it keeps as it is), of any ISA: an implementation made from another one by replacing a
piece of it (e.g. ARMv7's rows with `umaal`, `Impl/Bignum/Arm/Umaal.lean`),
proven by `Verified.subst` (`Proof/Framework/Subst.lean`).
-/

@[expose] public section

namespace VG

deriving instance DecidableEq for Code

/-- `c` with every occurrence of `a` replaced by `b`. -/
def Code.subst {I C : Type} [DecidableEq I] [DecidableEq C] (a b : Code I C) : Code I C → Code I C
  | .block is => if .block is = a then b else .block is
  | .seq x y => if .seq x y = a then b else .seq (Code.subst a b x) (Code.subst a b y)
  | .ite k t e => if .ite k t e = a then b else .ite k (Code.subst a b t) (Code.subst a b e)
  | .loop x k => if .loop x k = a then b else .loop (Code.subst a b x) k
  | .call n x => if .call n x = a then b else .call n (Code.subst a b x)
  | .frame i x j => if .frame i x j = a then b else .frame i (Code.subst a b x) j
  -- Not inside an indirect call, whose chain of functions (`next`) must stay
  -- one of indirect calls.
  | .icall i n x y => if .icall i n x y = a then b else .icall i n x y

end VG
