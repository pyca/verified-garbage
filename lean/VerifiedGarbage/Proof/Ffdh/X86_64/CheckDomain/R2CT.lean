module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.StagesCT

import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
meta import VerifiedGarbage.Proof.Ffdh.X86_64.R2
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH domain validation on x86-64: public precomputation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private def CH (p : CdP) (s : State) : Prop :=
  Inner p s ∧ s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .r10 = off (off p.B (inner p.w)) (slot p.w aN)

private theorem head_ok (p : CdP) (s : State) (h : Inner p s) : WP isa (.block r2Head) s (CH p) := by
  obtain ⟨mi, hw, hd, hm⟩ := h
  exact WP.mono (r2Head_ok (hw.mem.ctx hd).good (Nat.le_refl _)) fun t ⟨h12, h10, hmem, k⟩ =>
    ⟨⟨mi, hw.keep hmem k, (k.gpr (by decide)).trans hd, hm⟩, h12, h10⟩

private theorem work_r2 {p : CdP} {s : State} {mi : BitVec 64}
    (hw : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) (hm : p.mv = true)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 p.w) (h10 : s.gpr .r10 = off (off p.B (inner p.w)) (slot p.w aN)) :
    R2Pre ⟨⟨off p.B (inner p.w), slot p.w 8, p.w, mi⟩, p.P⟩ s := by
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  have hk := hw.base.k1
  have hk' := hw.base.k2
  obtain ⟨ho, _, hlo⟩ := valid_facts hm hk
  exact ⟨⟨(hw.mem.ctx hd).good, Nat.le_refl _⟩, show 2 ≤ p.w by omega, show p.w < 2 ^ 30 by omega,
    hw.xv.n, hw.xv.inv, h12, h10, ho, hlo⟩

private theorem ch_r2 {s₁ s₂ : State} (h : Two CH s₁ s₂) : Two R2Pre s₁ s₂ := by
  refine two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h
  obtain ⟨⟨mi₁, hw₁, hd₁, hm⟩, h12₁, h10₁⟩ := h₁
  obtain ⟨⟨mi₂, hw₂, hd₂, _⟩, h12₂, h10₂⟩ := h₂
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  have hk := hw₁.base.k1
  have ho := (valid_facts hm hk).1
  obtain rfl := xvals_minv (show 1 ≤ p.w by omega) ho hw₁.xv hw₂.xv
  exact ⟨_, work_r2 hw₁ hd₁ hm h12₁ h10₁, work_r2 hw₂ hd₂ hm h12₂ h10₂⟩

theorem r2_ct (M : Mont) (R : R2Impl M) :
    RelCT isa (Two Inner) (.seq (.block r2Head) R.code) fun _ _ => True := by
  refine RelCT.seq (R := Two CH)
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ h => by
      obtain ⟨_, _, hd, _⟩ := h; exact hd) (by taint_decide) head_ok)
    (R.ct.mono (fun _ _ h => ch_r2 h) fun _ _ h => h)

end VG.Proof.Ffdh.X86_64.CheckDomain
