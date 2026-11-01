module
public import VerifiedGarbage.Impl.AesXts.AArch64
public import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
public import VerifiedGarbage.Proof.AesCbc.AArch64.Call
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Xts.Contract

import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
import VerifiedGarbage.Proof.AesXts.AArch64.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit

/-!
# XTS-AES on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from `crypt_wp` and `crypt_ct`, a state satisfying the
precondition, and the shared contracts of `Spec/Xts/Contract.lean` (with no
stack: the call keeps the return address in `x30`, which the functions save
in the scratch buffer).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64

open VG VG.AArch64 VG.Impl.AesXts.AArch64
open VG.Proof.AesCbc (ciphOf aesWith_state aesInvWith_state)
open VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

theorem encrypt_keepsV (v : BlocksImpl) : (encrypt v.enc).allInstrs keepsV = true := by
  simp only [encrypt, crypt, batch, pass, Code.allInstrs, v.encKeepsV]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (modeAArch64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s' :=
  WP.withPreservedV (crypt_wp true v.encOk v.encNoFrames (fun R w m p => (aesWith_state R w m p).symm) hs)
    (encrypt_keepsV v)

/-- `Verified` against the shared contract, from correctness and constant time against
`modeAArch64 (xtsMode true)`. -/
theorem encrypt_verified_of {c : Prog isa}
    (ok : ∀ s, (modeAArch64 (AesXts.xtsMode true)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s')
    (ct : ConstantTime isa (modeAArch64 (AesXts.xtsMode true)).pre (modeAArch64 (AesXts.xtsMode true)).pub c) :
    Verified AArch64.target c (Proof.Xts.aesEncryptContract AArch64.abi) :=
  Verified.of_correct ok ct
    { pre := by sig_implies_pre [Proof.Xts.aesEncryptContract, Proof.Xts.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs]
      -- `xtsMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Proof.Xts.aesEncryptContract, Proof.Xts.aesSig, modeAArch64, AesXts.xtsMode, ciphOf, AArch64.abi,
          AArch64.argRegs]
        sig_reduce [Proof.Xts.aesEncryptContract, Proof.Xts.aesSig, modeAArch64, AesXts.xtsMode, ciphOf, AArch64.abi,
          AArch64.argRegs] at h
        sig_simp [Proof.Xts.aesEncryptContract, Proof.Xts.aesSig, modeAArch64, AesXts.xtsMode, ciphOf, AArch64.abi,
          AArch64.argRegs] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Proof.Xts.aesEncryptContract, Proof.Xts.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs]
      sat := by sig_implies_sat [Proof.Xts.aesEncryptContract, Proof.Xts.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs] [sat] using sat }

theorem encrypt_verified (v : BlocksImpl) :
    Verified AArch64.target (encrypt v.enc) (Proof.Xts.aesEncryptContract AArch64.abi) :=
  encrypt_verified_of (encrypt_correct v)
    (crypt_ct true v.encOk v.encCt v.encNoFrames fun R w m p => (aesWith_state R w m p).symm)

theorem decrypt_keepsV (v : BlocksImpl) : (decrypt v.dec).allInstrs keepsV = true := by
  simp only [decrypt, crypt, batch, pass, Code.allInstrs, v.decKeepsV]; decide +kernel

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (modeAArch64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa (decrypt v.dec) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode false)).post s s' :=
  WP.withPreservedV (crypt_wp false v.decOk v.decNoFrames (fun R w m p => (aesInvWith_state R w m p).symm) hs)
    (decrypt_keepsV v)

/-- `Verified` against the shared contract, from correctness and constant time against
`modeAArch64 (xtsMode false)`. -/
theorem decrypt_verified_of {c : Prog isa}
    (ok : ∀ s, (modeAArch64 (AesXts.xtsMode false)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode false)).post s s')
    (ct : ConstantTime isa (modeAArch64 (AesXts.xtsMode false)).pre (modeAArch64 (AesXts.xtsMode false)).pub c) :
    Verified AArch64.target c (Proof.Xts.aesDecryptContract AArch64.abi) :=
  Verified.of_correct ok ct
    { pre := by sig_implies_pre [Proof.Xts.aesDecryptContract, Proof.Xts.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs]
      -- `xtsMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Proof.Xts.aesDecryptContract, Proof.Xts.aesSig, modeAArch64, AesXts.xtsMode, ciphOf, AArch64.abi,
          AArch64.argRegs]
        sig_reduce [Proof.Xts.aesDecryptContract, Proof.Xts.aesSig, modeAArch64, AesXts.xtsMode, ciphOf, AArch64.abi,
          AArch64.argRegs] at h
        sig_simp [Proof.Xts.aesDecryptContract, Proof.Xts.aesSig, modeAArch64, AesXts.xtsMode, ciphOf, AArch64.abi,
          AArch64.argRegs] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Proof.Xts.aesDecryptContract, Proof.Xts.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs]
      sat := by sig_implies_sat [Proof.Xts.aesDecryptContract, Proof.Xts.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs] [sat] using sat }

theorem decrypt_verified (v : BlocksImpl) :
    Verified AArch64.target (decrypt v.dec) (Proof.Xts.aesDecryptContract AArch64.abi) :=
  decrypt_verified_of (decrypt_correct v)
    (crypt_ct false v.decOk v.decCt v.decNoFrames fun R w m p => (aesInvWith_state R w m p).symm)

end VG.Proof.AesXts.AArch64
