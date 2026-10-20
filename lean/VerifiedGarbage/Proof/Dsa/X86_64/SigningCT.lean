module
public import VerifiedGarbage.Proof.Dsa.X86_64.FailureCT
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningPublic

import VerifiedGarbage.Proof.Dsa.X86_64.SigningReadyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant time of the complete signing entry point -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem SigningShaped.branch {reference : SigningCall} {s : State} (h : SigningShaped reference s) :
    eval .e s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change s.zf = _
  rw [hs.branch, ha.accepted]

def SigningCall.failure (c : SigningCall) : FailurePublic := ⟨c.layout.base, c.layout.fields .out, c.layout.qLen⟩

theorem SigningShaped.failure {reference : SigningCall} {s : State} (h : SigningShaped reference s) :
    FailurePre reference.failure s := by
  obtain ⟨c, ha, hs⟩ := h
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  have hr : s.gpr .rdi = c.layout.base := hs.rdi
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  rw [ha.layout] at hscr hr hf
  exact ⟨usedBytes, hscr, by decide, hr, hf .out, (hf .qLen).trans reference.layout.qLength⟩

theorem signingMain_ct (M : Mont) (Sq : MontS) : RelCT isa (Two SigningStart) (SignVerify.sign Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq signingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map SigningCall.failure (fun _ _ h => h.failure) signFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (signingSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64
