import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
import VerifiedGarbage.Proof.AesXts.X86_64.CT

/-!
# XTS-AES on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from `crypt_wp` and `crypt_ct`, a state satisfying the
precondition, and the shared contracts of `Spec/Xts/Contract.lean` (with 8
bytes of stack, for the return address of the call of the block function).
-/

namespace VG.Proof.AesXts.X86_64

open VG VG.X86_64 VG.Impl.AesXts.X86_64
open VG.Proof.AesCbc (ciphOf aesWith_state aesInvWith_state)
open VG.Proof.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem encrypt_mx (v : BlocksImpl) : (encrypt v.enc).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encrypt, crypt, batch, pass, Code.allInstrs, v.encMxcsr]; decide +kernel

theorem decrypt_mx (v : BlocksImpl) : (decrypt v.dec).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decrypt, crypt, batch, pass, Code.allInstrs, v.decMxcsr]; decide +kernel

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt v.enc).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encrypt, crypt, batch, pass, Code.all, v.encSpSafe]; decide +kernel

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt v.dec).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decrypt, crypt, batch, pass, Code.all, v.decSpSafe]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (modeX86_64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := crypt_wp true v.encOk v.encNosp v.encDepth
    (fun R w m p => (aesWith_state R w m p).symm) hs
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx v) he hg, hp⟩

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (modeX86_64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa (decrypt v.dec) s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := crypt_wp false v.decOk v.decNosp v.decDepth
    (fun R w m p => (aesInvWith_state R w m p).symm) hs
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx v) he hg, hp⟩

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86_64.target (encrypt v.enc) (Spec.Xts.aesEncryptContract X86_64.abi 8) :=
  Verified.of_correct (encrypt_correct v)
    (crypt_ct true v.encOk v.encCt v.encNosp v.encDepth fun R w m p => (aesWith_state R w m p).symm)
    { pre := by sig_implies_pre [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs]
      -- `xtsMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeX86_64, AesXts.xtsMode, ciphOf, X86_64.abi,
          X86_64.argRegs]
        sig_reduce [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeX86_64, AesXts.xtsMode, ciphOf,
          X86_64.abi, X86_64.argRegs] at h
        sig_simp [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeX86_64, AesXts.xtsMode, ciphOf, X86_64.abi,
          X86_64.argRegs] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs]
      sat := by sig_implies_sat [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs] [sat] using sat }

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86_64.target (decrypt v.dec) (Spec.Xts.aesDecryptContract X86_64.abi 8) :=
  Verified.of_correct (decrypt_correct v)
    (crypt_ct false v.decOk v.decCt v.decNosp v.decDepth fun R w m p => (aesInvWith_state R w m p).symm)
    { pre := by sig_implies_pre [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs]
      -- `xtsMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeX86_64, AesXts.xtsMode, ciphOf, X86_64.abi,
          X86_64.argRegs]
        sig_reduce [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeX86_64, AesXts.xtsMode, ciphOf,
          X86_64.abi, X86_64.argRegs] at h
        sig_simp [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeX86_64, AesXts.xtsMode, ciphOf, X86_64.abi,
          X86_64.argRegs] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs]
      sat := by sig_implies_sat [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs] [sat] using sat }

end VG.Proof.AesXts.X86_64
