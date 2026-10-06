import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacMain
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified

/-! Production P-256 Jacobian verification preserves the existing ABI and result contract. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem jacPre_of {s : State} (h : verifyAArch64.pre s) : VPre p256 s := by
  obtain ⟨h1,h2,h3,h4,h5,h6,held,fit,hdw⟩ := h
  exact ⟨h1,h2,h3,h4,h5,h6,⟨by rw [h1]; simp,held,fit,hdw _ (by simp)⟩⟩

theorem jacVerify_noCalls : verifyP256.noCalls=true := by lit_decide

theorem jacVerify_untouched : KeepsUntouched verifyP256 := by lit_decide

theorem jacVerify_keepsV : verifyP256.allInstrs keepsV=true := by lit_decide

theorem jacVerify_a64 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (s : State) (hs : verifyAArch64.pre s) :
    ∃ t s', Exec isa verifyP256 s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t,s',he,hsv,hpost⟩ := jacVerify_ok (p256_ok hI) (by decide) hL hT (jacPre_of hs)
  exact ⟨t,s',he,abiPreserved_of he jacVerify_noCalls jacVerify_untouched jacVerify_keepsV hsv,hpost⟩

end VG.Proof.Ecdsa.Verify.AArch64
