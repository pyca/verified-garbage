import VerifiedGarbage.Proof.AesCbc.X86.Verified
import VerifiedGarbage.Proof.AesCtr.X86.Body

/-!
# AES-CTR on x86: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from the loop AES-CBC's proofs share, a state satisfying the
precondition, and the shared contract of `Spec/Ctr/Contract.lean`, with 24
bytes of stack: each call of a block function pushes its five arguments and
the return address.
-/

namespace VG.Proof.AesCtr.X86

open VG VG.X86 VG.Impl.AesCtr.X86
open VG.Impl.AesCbc.X86 (whole blkCall)
open VG.Proof.AesCbc.X86
open VG.Proof.Aes.X86 (BlocksImpl)

theorem crypt_spSafe (v : BlocksImpl) : (crypt v.enc).all (fun i => !isa.writesSp i) = true := by
  simp only [crypt, whole, body, blkCall, Code.all, v.encSpSafe]
  decide +kernel

theorem crypt_verified (v : BlocksImpl) :
    Verified X86.target (crypt v.enc) (Spec.Ctr.aesContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => whole_wp (body_ok v) hs) (whole_ct (body_ok v) (body_ct v))
    { pre := by sig_implies_pre [Spec.Ctr.aesContract, Spec.Ctr.aesSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, modeX86]
      -- `ctrMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Ctr.aesContract, Spec.Ctr.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, modeX86, AesCtr.ctrMode]
        sig_reduce [Spec.Ctr.aesContract, Spec.Ctr.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, modeX86, AesCtr.ctrMode] at h
        sig_simp [Spec.Ctr.aesContract, Spec.Ctr.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, modeX86, AesCtr.ctrMode] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Ctr.aesContract, Spec.Ctr.aesSig, X86.abi, X86.argSlots,
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
        sig_implies_sat [Spec.Ctr.aesContract, Spec.Ctr.aesSig, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes, modeX86] [a0, a1, a2, a3, a4, a5, e, esp] using sat }

end VG.Proof.AesCtr.X86
