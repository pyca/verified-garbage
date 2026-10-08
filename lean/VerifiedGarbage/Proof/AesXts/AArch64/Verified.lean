import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
import VerifiedGarbage.Proof.AesXts.AArch64.Body

/-!
# XTS-AES on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from the loop AES-CBC's proofs share, a state satisfying the
precondition, and the shared contracts of `Spec/Xts/Contract.lean` (with no
stack: the call keeps the return address in `x30`, which the functions save
in the scratch buffer).
-/

namespace VG.Proof.AesXts.AArch64

open VG VG.AArch64 VG.Impl.AesXts.AArch64
open VG.Impl.AesCbc.AArch64 (whole)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

theorem encrypt_keepsV (v : BlocksImpl) : (encrypt v.enc).allInstrs keepsV = true := by
  simp only [encrypt, whole, body, Code.allInstrs, v.encKeepsV]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (modeAArch64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s' :=
  WP.withPreservedV (whole_wp (encBody_ok v) hs) (encrypt_keepsV v)

theorem encrypt_verified (v : BlocksImpl) :
    Verified AArch64.target (encrypt v.enc) (Spec.Xts.aesEncryptContract AArch64.abi) :=
  Verified.of_correct (encrypt_correct v) (whole_ct (encBody_ok v) (encBody_ct v))
    { pre := by sig_implies_pre [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs]
      -- `xtsMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeAArch64, AesXts.xtsMode, ciphOf, AArch64.abi,
          AArch64.argRegs]
        sig_reduce [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeAArch64, AesXts.xtsMode, ciphOf, AArch64.abi,
          AArch64.argRegs] at h
        sig_simp [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeAArch64, AesXts.xtsMode, ciphOf, AArch64.abi,
          AArch64.argRegs] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs]
      sat := by sig_implies_sat [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs] [sat] using sat }

theorem decrypt_keepsV (v : BlocksImpl) : (decrypt v.dec).allInstrs keepsV = true := by
  simp only [decrypt, whole, body, Code.allInstrs, v.decKeepsV]; decide +kernel

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (modeAArch64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa (decrypt v.dec) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode false)).post s s' :=
  WP.withPreservedV (whole_wp (decBody_ok v) hs) (decrypt_keepsV v)

theorem decrypt_verified (v : BlocksImpl) :
    Verified AArch64.target (decrypt v.dec) (Spec.Xts.aesDecryptContract AArch64.abi) :=
  Verified.of_correct (decrypt_correct v) (whole_ct (decBody_ok v) (decBody_ct v))
    { pre := by sig_implies_pre [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs]
      -- `xtsMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeAArch64, AesXts.xtsMode, ciphOf, AArch64.abi,
          AArch64.argRegs]
        sig_reduce [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeAArch64, AesXts.xtsMode, ciphOf, AArch64.abi,
          AArch64.argRegs] at h
        sig_simp [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeAArch64, AesXts.xtsMode, ciphOf, AArch64.abi,
          AArch64.argRegs] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs]
      sat := by sig_implies_sat [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs] [sat] using sat }

end VG.Proof.AesXts.AArch64
