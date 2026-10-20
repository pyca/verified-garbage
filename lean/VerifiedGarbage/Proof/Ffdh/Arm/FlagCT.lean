module

public import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! Relate native validation branches through their public boolean result. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem ifFlag_known_ct {P : State → Prop} {yes no : Prog isa} (b : Bool)
    (flag : ∀ s, P s → s.gpr .r11 = if b then 1 else 0)
    (preserve : ∀ s t, P s → t.mem = s.mem → Rest [] s t → P t)
    (taken : b = true → RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) yes (fun _ _ => True))
    (other : b = false → RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) no (fun _ _ => True)) :
    RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag yes no) (fun _ _ => True) := by
  let Q := fun s : State => P s ∧ s.z = !b
  have test := testFlag_ct.mono (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ _ => trivial) (fun _ _ h => h)
  have wp (s : State) (h : P s) : WP isa VG.Impl.Ffdh.Arm.Domain.testFlag s Q := by
    refine WP.mono (testFlag_ok s) ?_
    rintro t ⟨⟨zero, mem⟩, rest⟩
    refine ⟨preserve s t h mem rest, ?_⟩
    rw [zero, flag s h]
    cases b <;> rfl
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .ne yes no) (fun _ _ => True) := by
    apply iteKnown_ct b (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro hb
      exact (taken hb).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro hb
      exact (other hb).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.ifFlag
  exact relCT_chain test wp wp branches

end VG.Proof.Ffdh.Arm
