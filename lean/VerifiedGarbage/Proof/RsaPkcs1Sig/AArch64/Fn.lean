module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Fn
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
public import VerifiedGarbage.Proof.Rsa.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.AArch64.SideFillT
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # RSASSA-PKCS1-v1_5 with a precomputed key on AArch64: the functions as emitted

Each function of `Impl.RsaPkcs1Sig.AArch64.Fn`, with any implementation of
the RSA operation it calls, meets its contract in constant time and returns
without secret residue (`VerifiedScrubbed`), which is what its registration
binds. What the cleanup needs of the code is its own instructions',
evaluated once with nothing in the place of the function it calls, and the
implementation's (`CrtImpl.crtPSide`, `PublicImpl.side`). -/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64

open VG VG.AArch64 VG.AArch64.ScrubAll VG.Proof.Rsa.AArch64

/-- `vg_rsa_pkcs1_sign_precomputed` as emitted, cleanup included. -/
theorem signPrecomputed_scrubbed (v : CrtImpl) :
    VerifiedScrubbed target (Impl.RsaPkcs1Sig.AArch64.Fn.signPrecomputed v.toCrt)
      (Spec.RsaPkcs1Sig.signPrecomputedContract abi 4400) 32 := by
  obtain ⟨hs, hd⟩ := side_depth_of_fill2 (c := Impl.RsaPkcs1Sig.AArch64.Sign.codeP v.privPName v.privP)
    (a := .call v.privPName v.privP) (b := .block []) (da := 203) (db := 0) (d := 275)
    (e := Impl.RsaPkcs1Sig.AArch64.Sign.codeP "" (.block [])) (by kernel_rfl) (privP_side v) (privP_depth v)
    (by kernel_rfl) (Nat.le_refl _) (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  exact verifiedScrubbedOfL (W := 4400) (Sgn.signPrecomputed_verified (privPOf v)) (Proof.Rsa.AArch64.Scrub.pkcs1SignOk _)
    (by decide) (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (.inr (.inl rfl))

/-- `vg_rsa_pkcs1_verify_precomputed` as emitted, cleanup included. -/
theorem verifyPrecomputed_scrubbed (v : PublicImpl) :
    VerifiedScrubbed target (Impl.RsaPkcs1Sig.AArch64.Fn.verifyPrecomputed v.name v.code)
      (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi 2144) 32 := by
  obtain ⟨hs, hd⟩ := side_depth_of_fill2 (c := Impl.RsaPkcs1Sig.AArch64.Precomputed.code v.name v.code)
    (a := .call v.name v.code) (b := .block []) (da := 0) (db := 0) (d := 134)
    (e := Impl.RsaPkcs1Sig.AArch64.Precomputed.code "" (.block [])) (by kernel_rfl) v.side (Nat.le_of_eq v.depth)
    (by kernel_rfl) (Nat.le_refl _) (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  exact verifiedScrubbedOf (W := 2144) (Pc.code_verified (pdOf v)) (Proof.Rsa.AArch64.Scrub.pkcs1VerifyOk _)
    (by decide) (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (.inr (.inl rfl))

/-- `vg_rsa_pkcs1_recover_precomputed` as emitted, cleanup included. -/
theorem recoverPrecomputed_scrubbed (v : PublicImpl) :
    VerifiedScrubbed target (Impl.RsaPkcs1Sig.AArch64.Fn.recoverPrecomputed v.name v.code)
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi 2144) 32 := by
  obtain ⟨hs, hd⟩ := side_depth_of_fill2 (c := Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed.code v.name v.code)
    (a := .call v.name v.code) (b := .block []) (da := 0) (db := 0) (d := 134)
    (e := Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed.code "" (.block [])) (by kernel_rfl) v.side
    (Nat.le_of_eq v.depth) (by kernel_rfl) (Nat.le_refl _) (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  exact verifiedScrubbedOf (W := 2144) (RecPc.code_verified (pdOf v)) (Proof.Rsa.AArch64.Scrub.pkcs1RecoverOk _)
    (by decide) (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (.inr (.inl rfl))

end VG.Proof.RsaPkcs1Sig.AArch64
