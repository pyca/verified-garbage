import VerifiedGarbage.Proof.AesCbc.X86.Verified
import VerifiedGarbage.Proof.AesXts.X86.Body

/-!
# XTS-AES on x86: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from the loop AES-CBC's proofs share, a state satisfying the
precondition, and the shared contracts of `Spec/Xts/Contract.lean`, with 24
bytes of stack: each call of a block function pushes its five arguments and
the return address.
-/

namespace VG.Proof.AesXts.X86

open VG VG.X86 VG.Impl.AesXts.X86
open VG.Impl.AesCbc.X86 (whole blkCall)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86
open VG.Proof.Aes.X86 (BlocksImpl)

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt v.enc).all (fun i => !isa.writesSp i) = true := by
  simp only [encrypt, whole, body, blkCall, Code.all, v.encSpSafe]
  decide +kernel

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86.target (encrypt v.enc) (Spec.Xts.aesEncryptContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => whole_wp (encBody_ok v) hs) (whole_ct (encBody_ok v) (encBody_ct v))
    { pre := by sig_implies_pre [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, modeX86]
      -- `xtsMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, modeX86, AesXts.xtsMode, ciphOf]
        sig_reduce [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, modeX86, AesXts.xtsMode, ciphOf] at h
        sig_simp [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, modeX86, AesXts.xtsMode, ciphOf] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, modeX86]
      sat := by
        have a0 : arg sat 0 = 0x1000 := by decide
        have a1 : arg sat 1 = 10 := by decide
        have a2 : arg sat 2 = 0x2000 := by decide
        have a3 : arg sat 3 = 0x3000 := by decide
        have a4 : arg sat 4 = 0 := by decide
        have a5 : arg sat 5 = 0x4000 := by decide
        have e : argAddr sat 0 = 0x8004 := by decide
        have esp : sat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes, modeX86] [a0, a1, a2, a3, a4, a5, e, esp] using sat }

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt v.dec).all (fun i => !isa.writesSp i) = true := by
  simp only [decrypt, whole, body, blkCall, Code.all, v.decSpSafe]
  decide +kernel

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86.target (decrypt v.dec) (Spec.Xts.aesDecryptContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => whole_wp (decBody_ok v) hs) (whole_ct (decBody_ok v) (decBody_ct v))
    { pre := by sig_implies_pre [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, modeX86]
      -- `xtsMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, modeX86, AesXts.xtsMode, ciphOf]
        sig_reduce [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, modeX86, AesXts.xtsMode, ciphOf] at h
        sig_simp [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, modeX86, AesXts.xtsMode, ciphOf] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, modeX86]
      sat := by
        have a0 : arg sat 0 = 0x1000 := by decide
        have a1 : arg sat 1 = 10 := by decide
        have a2 : arg sat 2 = 0x2000 := by decide
        have a3 : arg sat 3 = 0x3000 := by decide
        have a4 : arg sat 4 = 0 := by decide
        have a5 : arg sat 5 = 0x4000 := by decide
        have e : argAddr sat 0 = 0x8004 := by decide
        have esp : sat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes, modeX86] [a0, a1, a2, a3, a4, a5, e, esp] using sat }

end VG.Proof.AesXts.X86
