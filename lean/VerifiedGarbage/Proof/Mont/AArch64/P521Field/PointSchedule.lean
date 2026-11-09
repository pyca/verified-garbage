module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist

/-! Compose checked instruction reorderings through straight-line contexts. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64

theorem append_run_eq {a b c d : List Instr}
    (ha : ∀s,runBlock isa a s=runBlock isa b s)
    (hc : ∀s,runBlock isa c s=runBlock isa d s) :
    ∀s,runBlock isa (a++c) s=runBlock isa (b++d) s := by
  have hf : runBlock isa c=runBlock isa d := funext hc
  intro s
  rw [VG.AArch64.Interleave.runBlock_append,VG.AArch64.Interleave.runBlock_append,ha s,hf]

end VG.Proof.Mont.AArch64.P521Field
