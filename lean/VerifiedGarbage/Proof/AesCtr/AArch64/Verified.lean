import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
import VerifiedGarbage.Proof.AesCtr.AArch64.CT

/-!
# AES-CTR on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of
`vg_aes_ctr32`), from `crypt_wp` and `crypt_ct`, a state satisfying the
precondition, and the shared contract of `Spec/Ctr/Contract.lean` (with no
stack: the call keeps the return address in `x30`, which the function saves
in the scratch buffer), whose `leak` (the counter block's last four bytes)
gives the agreement on the last 32 bits of the counter block `crypt_ct`
assumes (`ctrPub`).
-/

namespace VG.Proof.AesCtr.AArch64

open VG VG.AArch64 VG.Impl.AesCtr.AArch64
open VG.Impl.AesCbc.AArch64 (whole)
open VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

theorem crypt_keepsV (v : Ctr32Impl) : (crypt v.callee).allInstrs keepsV = true := by
  simp only [crypt, whole, body, Code.allInstrs, v.keepsV]; decide +kernel

theorem crypt_correct (v : Ctr32Impl) (s : State) (hs : (modeAArch64 AesCtr.ctrMode).pre s) :
    ∃ t s', Exec isa (crypt v.callee) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 AesCtr.ctrMode).post s s' :=
  WP.withPreservedV (crypt_wp v hs) (crypt_keepsV v)

theorem crypt_verified (v : Ctr32Impl) :
    Verified AArch64.target (crypt v.callee) (Spec.Ctr.aesContract AArch64.abi) :=
  Verified.of_correct (k := { modeAArch64 AesCtr.ctrMode with pub := ctrPub }) (crypt_correct v) (crypt_ct v)
    { pre := by sig_implies_pre [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs]
      -- `ctrMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeAArch64, AesCtr.ctrMode, AArch64.abi,
          AArch64.argRegs]
        sig_reduce [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeAArch64, AesCtr.ctrMode, AArch64.abi,
          AArch64.argRegs] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by
        have hm : ∀ s₁ s₂, (Spec.Ctr.aesContract AArch64.abi).pre s₁ → (Spec.Ctr.aesContract AArch64.abi).pre s₂ →
            (Spec.Ctr.aesContract AArch64.abi).pub s₁ s₂ → (modeAArch64 AesCtr.ctrMode).pub s₁ s₂ := by
          sig_implies_pub [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeAArch64, AArch64.abi, AArch64.argRegs]
        intro s₁ s₂ h₁ h₂ h
        refine ⟨hm s₁ s₂ h₁ h₂ h, ?_⟩
        sig_pub [Spec.Ctr.aesContract, Spec.Ctr.aesSig, Spec.Ctr.ctrLeak, AArch64.abi, AArch64.argRegs] at h
        sig_split h
        exact AesCtr.lo32_of_leak (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _)
          (by assumption)
      sat := by sig_implies_sat [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs] [sat] using sat }

end VG.Proof.AesCtr.AArch64
