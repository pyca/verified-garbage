module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
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
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSAES-PKCS1-v1_5 on AArch64: what its scrubbed functions clear

The registers the tails of decryption and of encryption with random padding
clear, and what `ScrubAll.scrubAllOf` needs of their code (`scrubSide`), for
every implementation they are registered with: evaluated here, by the
kernel, so that the emitter works out nothing.
-/

-- separate module: the kernel's evaluation of the scrub's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

/-- The registers decryption's tail clears: those it may write, with every
implementation of SHA-256 and of the private-key operation (`decryptSide`). -/
def decryptClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31], []⟩

/-- The registers the tail of encryption with random padding clears
(`encryptRandomSide`). -/
def encryptRandomClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v31], []⟩

/-- What `scrubAllOf` needs of decryption with each implementation of SHA-256's
compression and of the private-key operation. -/
theorem decryptSide (h : Proof.Sha256.AArch64.Compress) (hh : h ∈ Proof.Variants.Sha256Compress.AArch64.variants) (c : Proof.Rsa.AArch64.CrtImpl) (hc : c ∈ Proof.Variants.RsaPrivateCrt.AArch64.variants) :
    scrubSide (Impl.RsaPkcs1Enc.AArch64.Decrypt.codeP (Dec.HH h) (privPOf c).name (privPOf c).code)
      (Dec.decStackP (privPOf c)) (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits abi.ptrBits) decryptClear [] = true := by
  have e : (Proof.Variants.Sha256Compress.AArch64.variants.all fun h => Proof.Variants.RsaPrivateCrt.AArch64.variants.all fun c => 
      scrubSide (Impl.RsaPkcs1Enc.AArch64.Decrypt.codeP (Dec.HH h) (privPOf c).name (privPOf c).code)
      (Dec.decStackP (privPOf c)) (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits abi.ptrBits) decryptClear []) = true := by lit_decide
  exact List.all_eq_true.mp (List.all_eq_true.mp e h hh) c hc

/-- What `scrubAllOf` needs of encryption with random padding, with each
implementation of the public-key operation. -/
theorem encryptRandomSide (v : Proof.Rsa.AArch64.PublicImpl) (hv : v ∈ Proof.Variants.RsaPublicPrecomputed.AArch64.variants) :
    scrubSide (Impl.RsaPkcs1Enc.AArch64.Random.code (Rnd.encName (RsaPkcs1Sig.AArch64.pdOf v)) (Rnd.encCode (RsaPkcs1Sig.AArch64.pdOf v)))
      (Rnd.rndStack (RsaPkcs1Sig.AArch64.pdOf v).stack) (Spec.RsaPkcs1Enc.encryptRandomSig.retBits abi.ptrBits) encryptRandomClear [] = true := by
  have e : (Proof.Variants.RsaPublicPrecomputed.AArch64.variants.all fun v => 
      scrubSide (Impl.RsaPkcs1Enc.AArch64.Random.code (Rnd.encName (RsaPkcs1Sig.AArch64.pdOf v)) (Rnd.encCode (RsaPkcs1Sig.AArch64.pdOf v)))
      (Rnd.rndStack (RsaPkcs1Sig.AArch64.pdOf v).stack) (Spec.RsaPkcs1Enc.encryptRandomSig.retBits abi.ptrBits) encryptRandomClear []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

end VG.Proof.RsaPkcs1Enc.AArch64.Scrub
