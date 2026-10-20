module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Preserve public call-stack geometry through key-generation prefixes -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem KeyCallMemory.after_sp {p : Inputs} {s t : State}
    (h : KeyCallMemory p s) (sp : t.sp = s.sp) : KeyCallMemory p t := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, h.privateFits⟩ <;> rw [sp]
  · exact h.stack.fit
  · exact h.stack.separate
  · exact h.domain
  · exact h.privateValue
  · exact h.publicValue
  · exact h.entropy

theorem keyGenerateWP_calls {p : Inputs} {s : State} {code : Prog isa} {Q : State → Prop}
    (wp : WP isa code s Q) (calls : KeyCallMemory p s) :
    WP isa code s fun t => Q t ∧ KeyCallMemory p t := by
  obtain ⟨tr, t, run, post⟩ := wp
  exact ⟨tr, t, run, post, calls.after_sp (Exec.sp run)⟩

theorem keyGenerateCT_calls {p : Inputs} {A B : State → Prop} {code : Prog isa}
    (ct : RelCT isa (fun s t => A s ∧ B t ∧ s.sp = t.sp) code (fun _ _ => True)) :
    RelCT isa (fun s t => (A s ∧ KeyCallMemory p s) ∧
      (B t ∧ KeyCallMemory p t) ∧ s.sp = t.sp) code (fun _ _ => True) :=
  ct.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm
