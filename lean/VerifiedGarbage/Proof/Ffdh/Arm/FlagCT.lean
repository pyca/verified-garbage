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

theorem ifFlag_pair_ct {P₁ P₂ : State → Prop} {yes no : Prog isa} (b : Bool)
    (flag₁ : ∀ s, P₁ s → s.gpr .r11 = if b then 1 else 0)
    (flag₂ : ∀ s, P₂ s → s.gpr .r11 = if b then 1 else 0)
    (preserve₁ : ∀ s t, P₁ s → t.mem = s.mem → Rest [] s t → P₁ t)
    (preserve₂ : ∀ s t, P₂ s → t.mem = s.mem → Rest [] s t → P₂ t)
    (taken : b = true → RelCT isa (fun s t => P₁ s ∧ P₂ t ∧ s.sp = t.sp) yes (fun _ _ => True))
    (other : b = false → RelCT isa (fun s t => P₁ s ∧ P₂ t ∧ s.sp = t.sp) no (fun _ _ => True)) :
    RelCT isa (fun s t => P₁ s ∧ P₂ t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag yes no) (fun _ _ => True) := by
  let Q₁ := fun s : State => P₁ s ∧ s.z = !b
  let Q₂ := fun s : State => P₂ s ∧ s.z = !b
  have test := testFlag_ct.mono (P' := fun (s t : State) => P₁ s ∧ P₂ t ∧ s.sp = t.sp)
    (fun _ _ _ => trivial) (fun _ _ h => h)
  have wp₁ (s : State) (h : P₁ s) : WP isa VG.Impl.Ffdh.Arm.Domain.testFlag s Q₁ := by
    refine WP.mono (testFlag_ok s) ?_
    rintro t ⟨⟨zero, mem⟩, rest⟩
    refine ⟨preserve₁ s t h mem rest, ?_⟩
    rw [zero, flag₁ s h]; cases b <;> rfl
  have wp₂ (s : State) (h : P₂ s) : WP isa VG.Impl.Ffdh.Arm.Domain.testFlag s Q₂ := by
    refine WP.mono (testFlag_ok s) ?_
    rintro t ⟨⟨zero, mem⟩, rest⟩
    refine ⟨preserve₂ s t h mem rest, ?_⟩
    rw [zero, flag₂ s h]; cases b <;> rfl
  have branches : RelCT isa (fun s t => Q₁ s ∧ Q₂ t ∧ s.sp = t.sp)
      (.ite .ne yes no) (fun _ _ => True) := by
    apply iteKnownPair_ct b (fun s h => by simp only [eval, h.2, Bool.not_not])
      (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro hb
      exact (taken hb).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro hb
      exact (other hb).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.ifFlag
  exact relCT_chain test wp₁ wp₂ branches

end VG.Proof.Ffdh.Arm
