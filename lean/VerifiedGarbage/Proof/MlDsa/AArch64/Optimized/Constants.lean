import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep wp_vop wp_scalar)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- Retain the measured constant initialization, including its unused legacy
reciprocal vector, while exposing only the modulus needed by this transform. -/
theorem fastConsts_ok (s : State) : WP isa (.block fastConsts) s fun t =>
    (∀ e < 4, vword (t.v .v16) e = 8380417#32) ∧ t.mem=s.mem ∧ Keep [.x9,.x10] s t := by
  unfold fastConsts
  rw [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.consts_ok s) fun s₁ ⟨hc,hm₁,hk₁⟩ => ?_
  refine wp_scalar (by rfl) (VG.Proof.MlDsa.AArch64.Arith.movW_ok .x9 2149582593 s₁)
    fun s₂ ⟨⟨_,hm₂⟩,hk₂⟩ hv₂ => ?_
  refine wp_vop (d := .v20) rfl fun s₃ h₃ => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · intro e he
    rw [h₃.get .v16,hv₂,hc.q,VG.AArch64.vword_ofVWords _ _ _ _ he]
    rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  · rw [h₃.mem,hm₂,hm₁]
  · exact ((hk₁.trans hk₂).trans h₃.keep).mono

end VG.Proof.MlDsa.AArch64.Optimized
