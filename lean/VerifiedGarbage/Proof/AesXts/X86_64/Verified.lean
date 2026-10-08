import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
import VerifiedGarbage.Proof.AesXts.X86_64.Body

/-!
# XTS-AES on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from the loop AES-CBC's proofs share, a state satisfying the
precondition, and the shared contracts of `Spec/Xts/Contract.lean` (with 8
bytes of stack, for the return address of the call of the block function).
-/

namespace VG.Proof.AesXts.X86_64

open VG VG.X86_64 VG.Impl.AesXts.X86_64
open VG.Impl.AesCbc.X86_64 (whole)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem encrypt_mx (v : BlocksImpl) : (encrypt v.enc).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encrypt, whole, body, Code.allInstrs, v.encMxcsr]; decide +kernel

theorem decrypt_mx (v : BlocksImpl) : (decrypt v.dec).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decrypt, whole, body, Code.allInstrs, v.decMxcsr]; decide +kernel

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt v.enc).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encrypt, whole, body, Code.all, v.encSpSafe]; decide +kernel

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt v.dec).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decrypt, whole, body, Code.all, v.decSpSafe]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (modeX86_64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := whole_wp (encBody_ok v) hs
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx v) he hg, hp⟩

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (modeX86_64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa (decrypt v.dec) s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := whole_wp (decBody_ok v) hs
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx v) he hg, hp⟩

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86_64.target (encrypt v.enc) (Spec.Xts.aesEncryptContract X86_64.abi 8) :=
  Verified.of_correct (encrypt_correct v) (whole_ct (encBody_ok v) (encBody_ct v))
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
  Verified.of_correct (decrypt_correct v) (whole_ct (decBody_ok v) (decBody_ct v))
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
