module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Interleaving two blocks of AArch64 code

`weave a b` merges `a` and `b`, keeping each at the same relative progress, so
that an out-of-order core finds instructions of both in its window. Blocks
whose footprints are independent run as `a` and then `b`
(`Proof/Framework/AArch64/Interleave.lean`, `WP.weave`).
-/

@[expose] public section

namespace VG.Impl.AArch64Weave

open VG.AArch64

/-- Interleave `a` and `b`, keeping each at the same relative progress, `i`
instructions of `a` (of `n`) and `j` of `b` (of `m`) taken. -/
def weaveGo (n m : Nat) : Nat → Nat → Nat → List Instr → List Instr → List Instr
  | 0, _, _, a, b => a ++ b
  | _ + 1, _, _, [], b => b
  | _ + 1, _, _, x :: a, [] => x :: a
  | f + 1, i, j, x :: a, y :: b =>
    if i * m ≤ j * n then x :: weaveGo n m f (i + 1) j a (y :: b) else y :: weaveGo n m f i (j + 1) (x :: a) b

def weave (a b : List Instr) : List Instr := weaveGo a.length b.length (a.length + b.length) 0 0 a b

end VG.Impl.AArch64Weave
