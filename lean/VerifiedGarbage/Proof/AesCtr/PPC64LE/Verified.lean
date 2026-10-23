module

public import VerifiedGarbage.Impl.AesCtr.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Proof.AesCtr.Spec
public import VerifiedGarbage.Spec.Ctr.Contract
import VerifiedGarbage.Proof.AesCtr.PPC64LE.CT
import VerifiedGarbage.Proof.AesCtr.PPC64LE.Iter
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Verified
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# AES-CTR on PPC64LE: `Verified`

Correctness and constant time, from `crypt_wp` and `crypt_ct`, a state
satisfying the precondition, and the shared contract of
`Spec/Ctr/Contract.lean` (with no stack: a call stores nothing in memory),
whose `leak` (the counter block's last four bytes) gives the agreement on
the last 32 bits of the counter block `crypt_ct` assumes (`ctrPub`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCtr.PPC64LE
open VG.Proof.AesCbc.PPC64LE

theorem crypt_correct (s : State) (hs : (modePPC64LE AesCtr.ctrMode).pre s) :
    ∃ t s', Exec isa crypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE AesCtr.ctrMode).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := crypt_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem crypt_verified : Verified PPC64LE.target crypt (Spec.Ctr.aesContract PPC64LE.abi) :=
  Verified.of_correct (k := { modePPC64LE AesCtr.ctrMode with pub := ctrPub }) crypt_correct crypt_ct
    { pre := by sig_implies_pre [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modePPC64LE, PPC64LE.abi,
        PPC64LE.argRegs]
      -- `ctrMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modePPC64LE, AesCtr.ctrMode, PPC64LE.abi,
          PPC64LE.argRegs]
        sig_reduce [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modePPC64LE, AesCtr.ctrMode, PPC64LE.abi,
          PPC64LE.argRegs] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by
        have hm : ∀ s₁ s₂, (Spec.Ctr.aesContract PPC64LE.abi).pre s₁ → (Spec.Ctr.aesContract PPC64LE.abi).pre s₂ →
            (Spec.Ctr.aesContract PPC64LE.abi).pub s₁ s₂ → (modePPC64LE AesCtr.ctrMode).pub s₁ s₂ := by
          sig_implies_pub [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
        intro s₁ s₂ h₁ h₂ h
        refine ⟨hm s₁ s₂ h₁ h₂ h, ?_⟩
        sig_pub [Spec.Ctr.aesContract, Spec.Ctr.aesSig, Spec.Ctr.ctrLeak, PPC64LE.abi, PPC64LE.argRegs] at h
        sig_split h
        exact AesCtr.lo32_of_leak (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _)
          (by assumption)
      sat := by sig_implies_sat [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modePPC64LE, PPC64LE.abi,
        PPC64LE.argRegs] [sat] using sat }

end VG.Proof.AesCtr.PPC64LE
