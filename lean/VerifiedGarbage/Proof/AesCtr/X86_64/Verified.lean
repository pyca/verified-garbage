import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
import VerifiedGarbage.Proof.AesCtr.X86_64.Body

/-!
# AES-CTR on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from the loop AES-CBC's proofs share, a state satisfying the
precondition, and the shared contract of `Spec/Ctr/Contract.lean` (with 8
bytes of stack, for the return address of the call of the block function).
-/

namespace VG.Proof.AesCtr.X86_64

open VG VG.X86_64 VG.Impl.AesCtr.X86_64
open VG.Impl.AesCbc.X86_64 (whole)
open VG.Proof.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem crypt_mx (v : BlocksImpl) : (crypt v.enc).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [crypt, whole, body, Code.allInstrs, v.encMxcsr]; decide +kernel

theorem crypt_spSafe (v : BlocksImpl) : (crypt v.enc).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [crypt, whole, body, Code.all, v.encSpSafe]; decide +kernel

theorem crypt_correct (v : BlocksImpl) (s : State) (hs : (modeX86_64 AesCtr.ctrMode).pre s) :
    ∃ t s', Exec isa (crypt v.enc) s t s' ∧ abiPreserved s s' ∧ (modeX86_64 AesCtr.ctrMode).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := whole_wp (body_ok v) hs
  exact ⟨t, s', he, abiPreserved_of_exec (crypt_mx v) he hg, hp⟩

theorem crypt_verified (v : BlocksImpl) :
    Verified X86_64.target (crypt v.enc) (Spec.Ctr.aesContract X86_64.abi 8) :=
  Verified.of_correct (crypt_correct v) (whole_ct (body_ok v) (body_ct v))
    { pre := by sig_implies_pre [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeX86_64, X86_64.abi, X86_64.argRegs]
      -- `ctrMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeX86_64, AesCtr.ctrMode, X86_64.abi, X86_64.argRegs]
        sig_reduce [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeX86_64, AesCtr.ctrMode, X86_64.abi,
          X86_64.argRegs] at h
        sig_simp [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeX86_64, AesCtr.ctrMode, X86_64.abi,
          X86_64.argRegs] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeX86_64, X86_64.abi, X86_64.argRegs]
      sat := by sig_implies_sat [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs] [sat] using sat }

end VG.Proof.AesCtr.X86_64
