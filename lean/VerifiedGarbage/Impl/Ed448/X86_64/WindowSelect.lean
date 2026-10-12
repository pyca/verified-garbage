module

public import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase

/-! Direct constant-time coordinate selection, without temporary field-slot writes. -/

@[expose] public section

namespace VG.Impl.Ed448.X86_64.Window

open VG.X86_64
open VG.Impl.X448.X86_64 (W sc slot loads stores)

/-- Keep the loaded words when the mask is nonzero; otherwise reload the old coordinate. -/
def retain (o : Nat) : List Instr :=
  [.alu .test .rcx (.reg .rcx)] ++
    (W.zip (List.range 7)).map fun (r, i) => .cmov .e r (.mem (sc (o + 8 * i)))

def selectMem (o a : Nat) : List Instr := loads a W ++ retain o ++ stores o W

def selectConst (o : Nat) (v : Spec.X448.Fe) : List Instr :=
  ((W.zip (words7 v.val)).map fun (r, x) => .movImm64 r x) ++ retain o ++ stores o W

end VG.Impl.Ed448.X86_64.Window
