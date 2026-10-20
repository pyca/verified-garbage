module
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingPublic

import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingReadyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingPublic
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingReadyCT

/-! # Constant time of the complete verifying entry point -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem VerifyingShaped.branch {reference : VerifyingCall} {s : State} (h : VerifyingShaped reference s) :
    eval .e s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change s.zf = _
  rw [hs.branch, ha.accepted]

theorem VerifyingShaped.rdi {reference : VerifyingCall} {s : State} (h : VerifyingShaped reference s) :
    s.gpr .rdi = reference.layout.base := by
  obtain ⟨c, ha, hs⟩ := h
  exact hs.rdi.trans (congrArg ExecutionLayout.base ha.layout)

theorem verifyFailure_ct : RelCT isa (Two (fun B : Addr => fun s => s.gpr .rdi = B))
    (.block (([.mov32 .rax (.imm 0)] : List Instr) ++ VG.Impl.Bignum.X86_64.Public.exit))
    (fun _ _ => True) :=
  two_taint [.rdi] (pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)) (by taint_decide)

theorem verifyingMain_ct (M : Mont) (Sq : MontS) : RelCT isa (Two VerifyingStart) (SignVerify.verify Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq verifyingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map (fun c : VerifyingCall => c.layout.base) (fun _ _ h => h.rdi) verifyFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (verifyingSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64
