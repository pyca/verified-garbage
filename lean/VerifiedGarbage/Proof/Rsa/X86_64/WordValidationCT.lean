module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordValidationCtx
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTDefs
import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTPieces
import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTLoads
import VerifiedGarbage.Proof.Rsa.X86_64.WordShadowCT

-- separate module: isolate the reusable adapter context from validation main sequencing

/-! # The word adapter preserves the key-checks' constant-time context -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem wordValidationK_ct : RelCT isa (Two KK) WordValidation.code (Two KK) := by
  refine two_post (two_map (fun p : KPub => (⟨p.B, p.Z, p.w⟩ : VG.Proof.Rsa.X86_64.WordValidation.Pub))
    (fun _ _ h => by
      obtain ⟨s, minv, N, hc, hs⟩ := h
      exact ⟨minv, hc.good, hs.word_w1, hs.word_w2, hs.word_room⟩)
    VG.Proof.Rsa.X86_64.WordValidation.code_ct) ?_
  rintro p t ⟨s, minv, N, hc, hs⟩
  exact WP.mono (VG.Proof.Rsa.X86_64.WordValidation.code_ok hc.good hs.word_room hs.word_w1 hs.word_w2)
    fun t' ⟨_, hf, hk⟩ => ⟨s, minv, N, hc.wordFrame hs.word_room hf hk, hs⟩

/-- Loads and comparisons retain the same context before and after the adapter. -/
theorem wordQInv_ct : RelCT isa (Two KK) WordValidation.qinv (Two KK) := by
  unfold WordValidation.qinv
  exact kk_app (by simp [CheckKey.loadNum]) (by simp [CheckKey.eqOne])
    (kk_app (by simp [CheckKey.loadNum]) (by simp)
      (kk_app (by simp [CheckKey.loadNum]) (by simp [CheckKey.mulXR, VG.Impl.Rsa.X86_64.Crt.zeroAccs])
        (kk_app (by simp [CheckKey.loadNum]) (by simp [CheckKey.loadNum])
          (kk_app (by simp [CheckKey.loadNum]) (by simp [CheckKey.ltMask])
            (kk_app (by simp [CheckKey.loadNum]) (by simp [CheckKey.loadNum]) ld_PM ld_QI) ltXM) ld_QR) mulXRK_ct)
      wordValidationK_ct) eqOneK_ct

end VG.Proof.Rsa.X86_64.Key
