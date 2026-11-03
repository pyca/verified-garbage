module

public import VerifiedGarbage.Impl.Subst

/-! Replace inline code while keeping every named call and callee body intact. -/

@[expose] public section
namespace VG

/-- Substitute within a function, stopping at its named calls. -/
def Code.substLocal {I C : Type} [DecidableEq I] [DecidableEq C]
    (a b : Code I C) : Code I C → Code I C
  | .block is => if .block is = a then b else .block is
  | .seq x y => if .seq x y = a then b else .seq (Code.substLocal a b x) (Code.substLocal a b y)
  | .ite k t e => if .ite k t e = a then b else .ite k (Code.substLocal a b t) (Code.substLocal a b e)
  | .loop x k => if .loop x k = a then b else .loop (Code.substLocal a b x) k
  | .call n x => .call n x
  | .frame i x j => if .frame i x j = a then b else .frame i (Code.substLocal a b x) j
  | .icall i n x y => .icall i n x y

end VG
