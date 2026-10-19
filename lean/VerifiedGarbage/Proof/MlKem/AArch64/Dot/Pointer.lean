module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Term
public import VerifiedGarbage.Impl.MlKem.AArch64.Dot
public import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Impl.MlKem.AArch64

def pointers (fg : Nat × Nat) : List Instr :=
  ptrTo .x1 .x28 fg.1 ++ ptrTo .x2 .x28 fg.2 ++
    [.add .x .x1 .x1 .x12, .add .x .x2 .x2 .x12]

theorem pointers_ok {s : State} {fg : Nat × Nat}
    (hf : fg.1 < 65536) (hg : fg.2 < 65536) :
    WP isa (.block (pointers fg)) s fun s' =>
      Only [.x1, .x2] s s' ∧ s'.v = s.v ∧
      s'.gpr .x1 = s.gpr .x28 + BitVec.ofNat 64 fg.1 + s.gpr .x12 ∧
      s'.gpr .x2 = s.gpr .x28 + BitVec.ofNat 64 fg.2 + s.gpr .x12 := by
  refine WP.mono (WP.keepV (Q := fun s' => Only [.x1, .x2] s s' ∧
    s'.gpr .x1 = s.gpr .x28 + BitVec.ofNat 64 fg.1 + s.gpr .x12 ∧
    s'.gpr .x2 = s.gpr .x28 + BitVec.ofNat 64 fg.2 + s.gpr .x12) ?_ ?_) ?_
  · simp only [pointers, ptrTo]
    split <;> split <;> rfl
  · simp only [pointers, List.append_assoc]
    refine wp_ptrTo (by decide) hf fun s₁ h₁ e₁ => wp_ptrTo (by decide) hg fun s₂ h₂ e₂ =>
      wp_add fun s₃ h₃ e₃ => wp_add fun s₄ h₄ e₄ => wp_nil ?_
    refine ⟨(((h₁.trans h₂).trans h₃).trans h₄).mono, ?_, ?_⟩
    · rw [h₄.get .x1, e₃, h₂.get .x1, e₁, h₂.get .x12, h₁.get .x12]
    · rw [e₄, h₃.get .x2, e₂, h₁.get .x28, h₃.get .x12, h₂.get .x12, h₁.get .x12]
  · intro s' h
    exact ⟨h.1.1, h.2, h.1.2⟩

theorem term_partition (fg : Nat × Nat) :
    Impl.MlKem.AArch64.Dot.dotTerm fg = pointers fg ++ termCore := by
  simp only [Impl.MlKem.AArch64.Dot.dotTerm, pointers, termCore, loads, gather,
    accumulate, List.append_assoc, List.cons_append, List.nil_append]

end VG.Proof.MlKem.AArch64.Dot
