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
# RSAES-PKCS1-v1_5 on AArch64: encryption as emitted

`vg_rsa_pkcs1_encrypt_random` with its cleanup
(`Impl.RsaPkcs1Enc.AArch64.Fn`), with any implementation of the RSA
operation it calls: it meets its contract in constant time and returns
without secret residue (`VerifiedScrubbed`), which is what its registration
binds (decryption's is in `FrontScrub.lean`). What the cleanup
needs of the code is its own instructions', evaluated once with nothing in
the place of the functions it calls, and the implementations' (their
records').
-/

-- separate module: the kernel's evaluation of the scrub's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Scrub

open VG.AArch64 VG.AArch64.Scrub
open VG.Proof.RsaPkcs1Sig.AArch64 (privP_side privP_depth pdOf)

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
