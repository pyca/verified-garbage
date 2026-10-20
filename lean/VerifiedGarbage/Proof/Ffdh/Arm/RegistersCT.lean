module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Retain equality of registers untouched by native control and load blocks. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

def RegistersEqual (rs : List Reg) (s t : State) : Prop := ∀ r ∈ rs, s.gpr r = t.gpr r

theorem registers_keep_ct {P : State → State → Prop} {code : Prog isa} (rs : List Reg)
    (ct : RelCT isa P code (fun _ _ => True))
    (registers : ∀ s t, P s t → RegistersEqual rs s t) (sp : ∀ s t, P s t → s.sp = t.sp)
    (untouched : ∀ r ∈ rs, ∀ i ∈ instrs code, clobbers i r = false) (noCalls : code.noCalls = true) :
    RelCT isa P code (fun s t => RegistersEqual rs s t ∧ s.sp = t.sp) := by
  intro s t tr1 tr2 u v h e1 e2
  refine ⟨(ct s t tr1 tr2 u v h e1 e2).1, ?_, ?_⟩
  · intro r hr
    exact (VG.Arm.Exec.gpr (untouched r hr) e1 (.inl noCalls)).trans
      ((registers s t h r hr).trans (VG.Arm.Exec.gpr (untouched r hr) e2 (.inl noCalls)).symm)
  · exact (Exec.rdwr e1).2.2.trans ((sp s t h).trans (Exec.rdwr e2).2.2.symm)

end VG.Proof.Ffdh.Arm
