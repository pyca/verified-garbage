module
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic

import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointAbi
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointCT
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Verified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointLit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.Joint
public import VerifiedGarbage.Proof.Weierstrass.CombW
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
import VerifiedGarbage.Proof.Framework.LitShare

/-! The joint implementation satisfies the unchanged shared verification contract. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64

section
variable (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P256.curve)
include hL hT hI hO

theorem jointVerify_verified : Verified X86_64.target jointVerifyP256
    (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts) 8) :=
  Verified.of_inline (k₀ := verifyK₀) (by lit_decide) (fun s hs => jointVerify_x86 hL hT hI hO s (implies.pre _ hs))
    (jointVerify_ct hL hT hI hO) implies8 (fun _ h => Sig.clear_of_pre_consts h) (fun _ _ _ _ _ hp => hp)
    fun s₁ s₂ h₁ h₂ hp => (implies.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp).1

theorem jointVerify_verified_adx : Verified X86_64.target jointVerifyP256Adx
    (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts) 8) :=
  Verified.of_inline (k₀ := verifyK₀) (by lit_decide) (fun s hs => jointVerify_x86_adx hL hT hI hO s (implies.pre _ hs))
    (jointVerify_adx_ct hL hT hI hO) implies8 (fun _ h => Sig.clear_of_pre_consts h) (fun _ _ _ _ _ hp => hp)
    fun s₁ s₂ h₁ h₂ hp => (implies.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp).1

end
end VG.Proof.Ecdsa.Verify.X86_64
