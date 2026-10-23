module

import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignChallenge
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignExpand
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignNonce

/-!
# `vg_ed25519_sign_cached` on PPC64LE, with its frame as an argument

The setup, the three phases and the restores (`signCached_wp`): `out` then
holds `R ‖ S`, RFC 8032's signature (`Proof.Ed25519.sign_pipeline`), given that
`pk` is the seed's public key.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt)

theorem signCached_wp (C : ShaOK) {s : State} (hp : SignPre s) :
    WP isa signCached s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      bytesAt t.mem (s.gpr .r3) 64 = Spec.Ed25519.sign (bytesAt s.mem (s.gpr .r4) 32) (msgB s) := by
  have F192 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 192, 32⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  have F0 : Region.Sub ⟨s.gpr .r9, 32⟩ ⟨s.gpr .r9, 288⟩ := Region.sub_prefix (by decide)
  unfold signCached
  refine WP.seq (WP.mono (signSetup_ok hp) fun t₁ ⟨h₁, hk₁⟩ => ?_)
  refine WP.seq (WP.mono (signExpand_ok C hp h₁) fun t₂ ⟨h₂, f₂, hs₂, hp₂⟩ => ?_)
  have hk₂ : bytesAt t₂.mem (s.gpr .r9 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .r5) 32 := by
    rw [← hk₁]
    exact bytes_keep f₂ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.cF.symm.sub_left F192
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · exact hp.bF.symm.sub_left F192
  refine WP.seq (WP.mono (signNonce_ok C hp h₂ hp₂) fun t₃ ⟨h₃, f₃, hn₃, hr₃⟩ => ?_)
  have keep₃ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r9, 288⟩ →
      (Region.Disjoint ⟨p, 32⟩ ⟨s.gpr .r9 + BitVec.ofNat 64 64, 128⟩) →
      bytesAt t₃.mem p 32 = bytesAt t₂.mem p 32 := fun hs hd =>
    bytes_keep f₃ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.cF.symm.sub_left hs
      · exact hd
      · exact hp.bF.symm.sub_left hs
      · exact (hp.oF.symm.sub_left hs).sub_right (Region.sub_prefix (by decide))
  have hk₃ := (keep₃ F192 (Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))).trans hk₂
  have hs₃ := (keep₃ F0 (Offset.base_disjoint _ (by decide) (by decide))).trans hs₂
  refine WP.seq (WP.mono (signChallenge_ok C hp h₃ hr₃ hn₃ hs₃ hk₃) fun t₄ ⟨h₄, hR, hS⟩ => ?_)
  have hFw : (⟨s.gpr .r9, 288⟩ : Region) ∈ t₄.rd ++ t₄.wr := List.mem_append_right _ (sign_Fw hp h₄)
  have hrl : ∀ p ∈ restoreList 224 signRegs, p.2 + 8 ≤ 288 := by decide
  refine restore_ok h₄ (by decide) (h₄.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => in_base hFw (hrl p hp') (by have := hrl p hp'; omega))
    fun t₅ g₅ sp₅ lr₅ m₅ _ => ⟨g₅, sp₅, lr₅, ?_⟩
  rw [m₅, Proof.Ed25519.signatureBytes_split, hR, hS]
  exact Proof.Ed25519.sign_pipeline _ _ _ hp.pk

end VG.Proof.Ed25519.PPC64LE.Whole
