module

public import VerifiedGarbage.TCB.AArch64.Isa

/-! # The fixed-base comb as an internal function on AArch64

A curve's signature and its public key run the same comb for `[k]G`, so the
comb is one internal function, `vg_<curve>_comb`, which both call: its body
(`combCall`) runs the comb between keeping the return address, `x30`, in a
register the comb does not write (`LrSave`) and taking it back, since the comb
uses `x30` (for its tables' addresses) and its own calls change it. A comb
that never writes `x30` and calls nothing keeps it itself (`LrSave.none`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64

open VG.AArch64

/-- Where a comb that is a function keeps its return address: nowhere (it
keeps `x30`), in a general register, or in lane 0 of a SIMD register. -/
inductive LrSave
  | none
  | gpr (r : Reg)
  | vec (v : VReg)

/-- `x30` into the register `LrSave` names. -/
def LrSave.save : LrSave → List Instr
  | .none => []
  | .gpr r => [.addImm .x r .x30 0]
  | .vec v => [.vop (.ins .d2 v 0 .x30)]

/-- `x30` back from the register `LrSave` names. -/
def LrSave.restore : LrSave → List Instr
  | .none => []
  | .gpr r => [.addImm .x .x30 r 0]
  | .vec v => [.umov .x .x30 v 0]

/-- The function's code: the comb between keeping `x30` and taking it back. -/
def combFn (k : LrSave) (comb : Prog isa) : Prog isa :=
  match k with
  | .none => comb
  | k => .seq (.block k.save) (.seq comb (.block k.restore))

/-- A call of the comb's function `name` (`vg_<curve>_comb`). -/
def combCall (name : String) (k : LrSave) (comb : Prog isa) : Prog isa :=
  .call name (combFn k comb)

end VG.Impl.Ecdsa.AArch64
