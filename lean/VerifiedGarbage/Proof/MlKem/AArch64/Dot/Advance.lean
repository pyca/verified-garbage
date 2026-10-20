module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Store
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Compute
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64

def bump : List Instr :=
  [.addImm .x .x0 .x0 32, .addImm .x .x3 .x3 16,
   .addImm .x .x12 .x12 32, .subImm .x .x11 .x11 1]

theorem bump_ok (s : State) : WP isa (.block bump) s fun s' =>
    Only [.x0,.x3,.x12,.x11] s s' ∧ s'.v = s.v ∧
    s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 32 ∧
    s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 16 ∧
    s'.gpr .x12 = s.gpr .x12 + BitVec.ofNat 64 32 ∧
    s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1 := by
  refine WP.mono (WP.keepV (Q := fun s' => Only [.x0,.x3,.x12,.x11] s s' ∧
    s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 32 ∧
    s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 16 ∧
    s'.gpr .x12 = s.gpr .x12 + BitVec.ofNat 64 32 ∧
    s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1) (by decide) ?_) ?_
  · refine wp_addImm (by decide) fun s₁ h₁ e₁ => wp_addImm (by decide) fun s₂ h₂ e₂ =>
      wp_addImm (by decide) fun s₃ h₃ e₃ => wp_subImm (by decide) fun s₄ h₄ e₄ => wp_nil ?_
    exact ⟨(((h₁.trans h₂).trans h₃).trans h₄).mono,
      by rw [h₄.get .x0,h₃.get .x0,h₂.get .x0,e₁],
      by rw [h₄.get .x3,h₃.get .x3,e₂,h₁.get .x3],
      by rw [h₄.get .x12,e₃,h₂.get .x12,h₁.get .x12],
      by rw [e₄,h₃.get .x11,h₂.get .x11,h₁.get .x11]⟩
  · intro s' h; exact ⟨h.1.1,h.2,h.1.2⟩

def body (terms : List (Nat × Nat)) : List Instr := compute terms ++ store ++ bump

theorem dot_partition (out : Nat) (terms : List (Nat × Nat)) :
    Impl.MlKem.AArch64.Dot.dot out terms =
      .seq (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 out ++ Impl.MlKem.AArch64.vconsts ++
       ([.adrSym .x3 "VG_MLKEM_GAMMA", .movz .x .x11 32 0, .movz .x .x12 0 0] : List Instr)))
      (.loop (.block (body terms)) (.nonzero .x .x11)) := by
  simp only [Impl.MlKem.AArch64.Dot.dot,body,compute,clear,finish,store,bump,
    List.append_assoc,List.cons_append,List.nil_append,Impl.MlKem.AArch64.Dot.dotReduce]

end VG.Proof.MlKem.AArch64.Dot
