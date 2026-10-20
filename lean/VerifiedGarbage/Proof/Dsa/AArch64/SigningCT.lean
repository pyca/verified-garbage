module
public import VerifiedGarbage.Proof.Dsa.AArch64.FailureCT
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningPublic

import VerifiedGarbage.Proof.Dsa.AArch64.SigningReadyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant time of the complete signing entry point -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem SigningShaped.branch {reference : SigningCall} {s : State} (h : SigningShaped reference s) :
    eval (.zero .x .x3) s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change some (s.gpr .x3 == (0#64)) = _
  rw [hs.branch, ha.accepted]

def SigningCall.failure (c : SigningCall) : FailurePublic := ⟨c.layout.base, c.layout.fields .out, c.layout.qLen⟩

theorem SigningShaped.failure {reference : SigningCall} {s : State} (h : SigningShaped reference s) :
    FailurePre reference.failure s := by
  obtain ⟨c, ha, hs⟩ := h
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  have hr : s.gpr .x0 = c.layout.base := hs.x0
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  rw [ha.layout] at hscr hr hf
  exact ⟨usedBytes, hscr, by decide, hr, hf .out, (hf .qLen).trans reference.layout.qLength⟩

theorem signingMain_ct (M : Mont) : RelCT isa (Two SigningStart) (SignVerify.sign M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq signingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂, hsp⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map SigningCall.failure (fun _ _ h => h.failure) signFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (signingSuccess_ct M).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂, hsp⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval (.zero .x .x3) s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64
