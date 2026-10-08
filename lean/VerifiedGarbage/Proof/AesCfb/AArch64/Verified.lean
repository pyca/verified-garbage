import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
import VerifiedGarbage.Proof.AesCfb.AArch64.Body

/-!
# AES-CFB128 on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from the loop AES-CBC's proofs share, a state satisfying the
precondition, and the shared contracts of `Spec/Cfb/Contract.lean` (with no
stack: the calls keep the return address in `x30`, which each function
saves in the scratch buffer).
-/

namespace VG.Proof.AesCfb.AArch64

open VG VG.AArch64 VG.Impl.AesCfb.AArch64
open VG.Impl.AesCbc.AArch64 (whole)
open VG.Proof.AesCbc (cts)
open VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

theorem encrypt_keepsV (v : BlocksImpl) : (encrypt v.enc).allInstrs keepsV = true := by
  simp only [encrypt, whole, body, Code.allInstrs, v.encKeepsV]; decide +kernel

theorem decrypt_keepsV (v : BlocksImpl) : (decrypt v.enc).allInstrs keepsV = true := by
  simp only [decrypt, whole, body, Code.allInstrs, v.encKeepsV]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (modeAArch64 (cfbMode true)).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (cfbMode true)).post s s' :=
  WP.withPreservedV (whole_wp (encBody_ok v) hs) (encrypt_keepsV v)

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (modeAArch64 (cfbMode false)).pre s) :
    ∃ t s', Exec isa (decrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (cfbMode false)).post s s' :=
  WP.withPreservedV (whole_wp (decBody_ok v) hs) (decrypt_keepsV v)

theorem encrypt_verified (v : BlocksImpl) :
    Verified AArch64.target (encrypt v.enc) (Spec.Cfb.aesEncryptContract AArch64.abi) :=
  Verified.of_correct (encrypt_correct v) (whole_ct (encBody_ok v) (encBody_ct v)) (by
    sig_implies [Spec.Cfb.aesEncryptContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, modeAArch64, cfbMode, cfb, cts,
      AArch64.abi, AArch64.argRegs] [sat] using sat)

theorem decrypt_verified (v : BlocksImpl) :
    Verified AArch64.target (decrypt v.enc) (Spec.Cfb.aesDecryptContract AArch64.abi) :=
  Verified.of_correct (decrypt_correct v) (whole_ct (decBody_ok v) (decBody_ct v)) (by
    sig_implies [Spec.Cfb.aesDecryptContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, modeAArch64, cfbMode, cfb, cts,
      AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.AesCfb.AArch64
