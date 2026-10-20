module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Stages
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Stages
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.R2
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH public-key validation on x86-64: precomputation in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh VG.Proof.MlKem.X86_64

private def C6H (p : CpP) (s : State) : Prop :=
  C6 p s ∧ s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .r10 = off (off p.B (inner p.w)) (slot p.w aN)

private theorem c6_head (p : CpP) (s : State) (h : C6 p s) : WP isa (.block r2Head) s (C6H p) := by
  obtain ⟨mi, hI, hm, hq, hEp, hEl⟩ := h
  refine WP.mono (r2Head_ok hI.2.1.good (Nat.le_refl _)) fun t ⟨h12, h10, hmem, k⟩ => ?_
  exact ⟨⟨mi, hI.keep hmem k (by decide), hm, hq, by rw [hmem]; exact hEp, by rw [hmem]; exact hEl⟩, h12, h10⟩

/-- The two runs have the same modulus and hence the same negative inverse. -/
private theorem c6h_two_r2 {s₁ s₂ : State} (h : Two C6H s₁ s₂) : Two R2Pre s₁ s₂ := by
  refine two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h
  obtain ⟨⟨mi₁, hI₁, hm, _⟩, h12₁, h10₁⟩ := h₁
  obtain ⟨⟨mi₂, hI₂, _, _⟩, h12₂, h10₂⟩ := h₂
  have c := hI₁.1.ctx
  obtain ⟨hodd, _⟩ := valid_facts hm c.k1
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega
  have hk := c.k1
  obtain rfl := xvals_minv (show 1 ≤ p.w by omega) hodd hI₁.2.2.1 hI₂.2.2.1
  exact ⟨_, c6_r2 hI₁ hm h12₁ h10₁, c6_r2 hI₂ hm h12₂ h10₂⟩

theorem c6_r2_ct (M : Mont) (R : R2Impl M) :
    RelCT isa (Two C6) (.seq (.block r2Head) R.code) fun _ _ => True := by
  refine RelCT.seq (R := Two C6H)
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun p s ⟨_, hI, _⟩ => hI.2.1.rdi) (by taint_decide) c6_head)
    (R.ct.mono (fun _ _ h => c6h_two_r2 h) fun _ _ h => h)

end VG.Proof.Ffdh.X86_64.CheckPublic
