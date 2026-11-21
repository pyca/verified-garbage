module

public import VerifiedGarbage.Proof.Framework.AArch64.SideFill
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Fn
public import VerifiedGarbage.Proof.Rsa.AArch64.Scrub
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callees
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Precomputed
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Random
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Proof.Variants.Sha256Compress.AArch64
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCTBase
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# RSAES-PKCS1-v1_5 on AArch64: the functions as emitted

`vg_rsa_pkcs1_decrypt_precomputed` and `vg_rsa_pkcs1_encrypt_random` with
their cleanup (`Impl.RsaPkcs1Enc.AArch64.Fn`), with any implementation of
SHA-256's compression function and of the RSA operation they call: each
meets its contract in constant time and returns without secret residue
(`VerifiedScrubbed`), which is what its registration binds. What the cleanup
needs of the code is its own instructions', evaluated once with nothing in
the place of the functions it calls, and the implementations' (their
records').
-/

-- separate module: the kernel's evaluation of the scrub's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Scrub

open VG.AArch64 VG.AArch64.Scrub
open VG.Proof.RsaPkcs1Sig.AArch64 (privP_side privP_depth pdOf)

/-- `vg_rsa_pkcs1_decrypt_precomputed` as emitted, cleanup included. -/
theorem decryptPrecomputed_scrubbed (h : Proof.Sha256.AArch64.Compress) (c : Proof.Rsa.AArch64.CrtImpl) :
    VerifiedScrubbed target (Impl.RsaPkcs1Enc.AArch64.Fn.decryptPrecomputed h.name h.suffix h.code c.toCrt)
      (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi 3488) 32 := by
  obtain ⟨hs, hd⟩ := side_depth_of_fill2
    (c := Impl.RsaPkcs1Enc.AArch64.Decrypt.codeP (Impl.Scrypt.AArch64.sha256 h.name h.suffix h.code)
      c.privPName c.privP)
    (a := .call c.privPName c.privP) (b := .call h.name h.code) (da := 203) (db := 0) (d := 218)
    (e := Impl.RsaPkcs1Enc.AArch64.Decrypt.codeP
      (Impl.Scrypt.AArch64.sha256 "" h.suffix (.seq (.block []) (.block []))) "" (.block []))
    (by kernel_rfl) (privP_side c) (privP_depth c) h.side
    (Nat.le_of_eq (Proof.Pbkdf2.Md.AArch64.fdepth_of_noFrames h.noFrames)) (by kernel_rfl)
    (Nat.le_of_ble_eq_true (by kernel_rfl))
  exact verifiedScrubbedOf (W := 3488) (Dec.decP_verified h (privPOf c) (decP_sat' c))
    (Proof.Rsa.AArch64.Scrub.pkcs1DecryptOk _) (by decide)
    (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (.inr (.inl rfl))

/-- `vg_rsa_pkcs1_encrypt_random` as emitted, cleanup included. -/
theorem encryptRandom_scrubbed (v : Proof.Rsa.AArch64.PublicImpl) :
    VerifiedScrubbed target (Impl.RsaPkcs1Enc.AArch64.Fn.encryptRandom v.suffix v.name v.code)
      (Spec.RsaPkcs1Enc.encryptRandomContract abi 2208) 32 := by
  obtain ⟨hs, hd⟩ := side_depth_of_fill2
    (c := Impl.RsaPkcs1Enc.AArch64.Random.code ("vg_rsa_pkcs1_encrypt_precomputed" ++ v.suffix)
      (Impl.RsaPkcs1Enc.AArch64.Precomputed.code v.name v.code))
    (a := .call v.name v.code) (b := .block []) (da := 0) (db := 0) (d := 138)
    (e := Impl.RsaPkcs1Enc.AArch64.Random.code ("vg_rsa_pkcs1_encrypt_precomputed" ++ v.suffix)
      (Impl.RsaPkcs1Enc.AArch64.Precomputed.code "" (.block [])))
    (by kernel_rfl) v.side (Nat.le_of_eq v.depth) (by kernel_rfl) (Nat.le_refl _) (by kernel_rfl)
    (Nat.le_of_ble_eq_true (by kernel_rfl))
  exact verifiedScrubbedOf (W := 2208) (Rnd.code_verified (pdOf v) Enc.Pc.sat Rnd.sat)
    (Proof.Rsa.AArch64.Scrub.pkcs1EncryptRandomOk _) (by decide)
    (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (.inr (.inl rfl))

end VG.Proof.RsaPkcs1Enc.AArch64.Scrub
