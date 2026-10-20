module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.StagesCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.R2
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH exchange on x86-64: public precomputation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private def CH (p : ExP) (s : State) : Prop :=
  C1 p s ∧ s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .r10 = off (off p.B (inner p.w)) (slot p.w aN)

private theorem head_ok (p : ExP) (s : State) (h : C1 p s) : WP isa (.block r2Head) s (CH p) := by
  obtain ⟨⟨xb, mi, hb, hc, hv⟩, hm⟩ := h
  refine WP.mono (r2Head_ok hc.good (Nat.le_refl _)) fun t ⟨h12, h10, hmem, k⟩ => ?_
  exact ⟨⟨⟨xb, mi, hb.keep (by rw [hmem]; exact InScr.refl _ _ _) k (fun _ _ => by rw [hmem]),
    hc.of_frm (rs := []) (by rw [hmem]; exact Frm.refl _ _ _) (fun _ hr => by simp at hr) k.2.2 (k.gpr (by decide)),
    ⟨by rw [hmem]; exact hv.n, by rw [hmem]; exact hv.inv, by rw [hmem]; exact hv.one⟩⟩, hm⟩, h12, h10⟩

private theorem entered_r2 {p : ExP} {s : State} {xb : List Byte} {mi : BitVec 64}
    (hb : Base p xb s) (hc : SubCtx s p.B p.Z (inner p.w) p.w p.w mi)
    (hv : XVals s p.B (inner p.w) p.w mi p.P) (hm : p.mv = true)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 p.w) (h10 : s.gpr .r10 = off (off p.B (inner p.w)) (slot p.w aN)) :
    R2Pre ⟨⟨off p.B (inner p.w), slot p.w 8, p.w, mi⟩, p.P⟩ s := by
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold ExP.w; omega
  have hk := hb.k1
  have hk' := hb.k2
  obtain ⟨ho, _, hlo⟩ := valid_facts hm hk
  exact ⟨⟨hc.good, Nat.le_refl _⟩, show 2 ≤ p.w by omega, show p.w < 2 ^ 30 by omega, hv.n, hv.inv, h12, h10, ho, hlo⟩

private theorem ch_r2 {s₁ s₂ : State} (h : Two CH s₁ s₂) : Two R2Pre s₁ s₂ := by
  refine two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h
  obtain ⟨⟨⟨xb₁, mi₁, hb₁, hc₁, hv₁⟩, hm⟩, h12₁, h10₁⟩ := h₁
  obtain ⟨⟨⟨xb₂, mi₂, hb₂, hc₂, hv₂⟩, _⟩, h12₂, h10₂⟩ := h₂
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold ExP.w; omega
  have hk := hb₁.k1
  have ho := (valid_facts hm hk).1
  obtain rfl := xvals_minv (show 1 ≤ p.w by omega) ho hv₁ hv₂
  exact ⟨_, entered_r2 hb₁ hc₁ hv₁ hm h12₁ h10₁, entered_r2 hb₂ hc₂ hv₂ hm h12₂ h10₂⟩

theorem r2_ct (M : Mont) (R : R2Impl M) : RelCT isa (Two C1) (.seq (.block r2Head) R.code) (Two C2) := by
  refine two_post (RelCT.seq (R := Two CH)
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ h => by obtain ⟨⟨_, _, _, hc, _⟩, _⟩ := h; exact hc.rdi) (by taint_decide) head_ok)
    (R.ct.mono (fun _ _ h => ch_r2 h) fun _ _ h => h)) ?_
  intro p s h
  obtain ⟨⟨xb, hh⟩, hm⟩ := h
  exact WP.mono (entered_ready M R hh hm) fun _ ⟨hr, _⟩ => ⟨xb, hr⟩

end VG.Proof.Ffdh.X86_64.Exchange
