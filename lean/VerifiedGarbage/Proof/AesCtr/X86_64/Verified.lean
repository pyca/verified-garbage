import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
import VerifiedGarbage.Proof.AesCtr.X86_64.CT

/-!
# AES-CTR on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of
`vg_aes_ctr32`), from `crypt_wp` and `crypt_ct`, a state satisfying the
precondition, and the shared contract of `Spec/Ctr/Contract.lean` (with 8
bytes of stack, for the return address of the call of `vg_aes_ctr32`),
whose `leak` (the counter block's last four bytes) gives the agreement on
the last 32 bits of the counter block `crypt_ct` assumes (`ctrPub`).
-/

namespace VG.Proof.AesCtr.X86_64

open VG VG.X86_64 VG.Impl.AesCtr.X86_64
open VG.Proof.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem crypt_mx (v : Ctr32Impl) : (crypt v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [crypt, body, Code.allInstrs, v.mxcsr]; decide +kernel

theorem crypt_spSafe (v : Ctr32Impl) : (crypt v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [crypt, body, Code.all, v.spSafe]; decide +kernel

theorem crypt_correct (v : Ctr32Impl) (s : State) (hs : (modeX86_64 AesCtr.ctrMode).pre s) :
    ∃ t s', Exec isa (crypt v.callee) s t s' ∧ abiPreserved s s' ∧ (modeX86_64 AesCtr.ctrMode).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := crypt_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (crypt_mx v) he hg, hp⟩

theorem crypt_verified (v : Ctr32Impl) :
    Verified X86_64.target (crypt v.callee) (Spec.Ctr.aesContract X86_64.abi 8) :=
  Verified.of_correct (k := { modeX86_64 AesCtr.ctrMode with pub := ctrPub }) (crypt_correct v) (crypt_ct v)
    { pre := by sig_implies_pre [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeX86_64, X86_64.abi, X86_64.argRegs]
      -- `ctrMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeX86_64, AesCtr.ctrMode, X86_64.abi, X86_64.argRegs]
        sig_reduce [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeX86_64, AesCtr.ctrMode, X86_64.abi,
          X86_64.argRegs] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by
        have hm : ∀ s₁ s₂, (Spec.Ctr.aesContract X86_64.abi 8).pre s₁ → (Spec.Ctr.aesContract X86_64.abi 8).pre s₂ →
            (Spec.Ctr.aesContract X86_64.abi 8).pub s₁ s₂ → (modeX86_64 AesCtr.ctrMode).pub s₁ s₂ := by
          sig_implies_pub [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeX86_64, X86_64.abi, X86_64.argRegs]
        intro s₁ s₂ h₁ h₂ h
        refine ⟨hm s₁ s₂ h₁ h₂ h, ?_⟩
        sig_pub [Spec.Ctr.aesContract, Spec.Ctr.aesSig, Spec.Ctr.ctrLeak, X86_64.abi, X86_64.argRegs] at h
        sig_split h
        exact AesCtr.lo32_of_leak (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _)
          (by assumption)
      sat := by sig_implies_sat [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs] [sat] using sat }

end VG.Proof.AesCtr.X86_64
