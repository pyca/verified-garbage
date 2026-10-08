import VerifiedGarbage.Proof.AesCbc.X86.Verified
import VerifiedGarbage.Proof.AesCfb.X86.Body

/-!
# AES-CFB128 on x86: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from the loop AES-CBC's proofs share, a state satisfying the
precondition, and the shared contracts of `Spec/Cfb/Contract.lean`, with 24
bytes of stack: each call of a block function pushes its five arguments and
the return address.
-/

namespace VG.Proof.AesCfb.X86

open VG VG.X86 VG.Impl.AesCfb.X86
open VG.Impl.AesCbc.X86 (whole blkCall)
open VG.Impl.AesOfb.X86 (ivArgs)
open VG.Proof.AesCbc (cts)
open VG.Proof.AesCbc.X86
open VG.Proof.Aes.X86 (BlocksImpl)

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt v.enc).all (fun i => !isa.writesSp i) = true := by
  simp only [encrypt, whole, body, blkCall, Code.all, v.encSpSafe]
  decide +kernel

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt v.enc).all (fun i => !isa.writesSp i) = true := by
  simp only [decrypt, whole, body, blkCall, Code.all, v.encSpSafe]
  decide +kernel

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86.target (encrypt v.enc) (Spec.Cfb.aesEncryptContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => whole_wp (encBody_ok v) hs) (whole_ct (encBody_ok v) (encBody_ct v)) (by
    have a0 : arg sat 0 = 0x1000 := by decide
    have a1 : arg sat 1 = 10 := by decide
    have a2 : arg sat 2 = 0x2000 := by decide
    have a3 : arg sat 3 = 0x3000 := by decide
    have a4 : arg sat 4 = 0 := by decide
    have a5 : arg sat 5 = 0x4000 := by decide
    have e : argAddr sat 0 = 0x8004 := by decide
    have esp : sat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Cfb.aesEncryptContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, modeX86, cfbMode, cfb, cts] [a0, a1, a2, a3, a4, a5, e, esp] using sat)

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86.target (decrypt v.enc) (Spec.Cfb.aesDecryptContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => whole_wp (decBody_ok v) hs) (whole_ct (decBody_ok v) (decBody_ct v)) (by
    have a0 : arg sat 0 = 0x1000 := by decide
    have a1 : arg sat 1 = 10 := by decide
    have a2 : arg sat 2 = 0x2000 := by decide
    have a3 : arg sat 3 = 0x3000 := by decide
    have a4 : arg sat 4 = 0 := by decide
    have a5 : arg sat 5 = 0x4000 := by decide
    have e : argAddr sat 0 = 0x8004 := by decide
    have esp : sat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Cfb.aesDecryptContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, modeX86, cfbMode, cfb, cts] [a0, a1, a2, a3, a4, a5, e, esp] using sat)

end VG.Proof.AesCfb.X86
