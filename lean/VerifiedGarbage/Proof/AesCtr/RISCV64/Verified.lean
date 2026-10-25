module

public import VerifiedGarbage.Impl.AesCtr.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Proof.AesCtr.Spec
public import VerifiedGarbage.Spec.Ctr.Contract
import VerifiedGarbage.Proof.AesCtr.RISCV64.CT
import VerifiedGarbage.Proof.AesCtr.RISCV64.Iter
import VerifiedGarbage.Proof.AesCbc.RISCV64.Verified
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# AES-CTR on RISC-V: `Verified`

Correctness and constant time, from `crypt_wp` and `crypt_ct`, a state
satisfying the precondition, and the shared contract of
`Spec/Ctr/Contract.lean` (with no stack: a call stores nothing in memory, and
the return address is saved in the scratch buffer), whose `leak` (the counter
block's last four bytes) gives the agreement on the last 32 bits of the
counter block `crypt_ct` assumes (`ctrPub`), as on PPC64LE
(`Proof/AesCtr/PPC64LE/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.RISCV64

open VG VG.RISCV64 VG.Impl.AesCtr.RISCV64
open VG.Proof.AesCbc.RISCV64

theorem crypt_correct (s : State) (hs : (modeRISCV64 AesCtr.ctrMode).pre s) :
    ∃ t s', Exec isa crypt s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 AesCtr.ctrMode).post s s' := by
  obtain ⟨t, s', he, hg, hra, hp⟩ := crypt_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩

theorem crypt_verified : Verified RISCV64.target crypt (Spec.Ctr.aesContract RISCV64.abi) :=
  Verified.of_correct (k := { modeRISCV64 AesCtr.ctrMode with pub := ctrPub }) crypt_correct crypt_ct
    { pre := by sig_implies_pre [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeRISCV64, RISCV64.abi,
        RISCV64.argRegs]
      -- `ctrMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeRISCV64, AesCtr.ctrMode, RISCV64.abi,
          RISCV64.argRegs]
        sig_reduce [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeRISCV64, AesCtr.ctrMode, RISCV64.abi,
          RISCV64.argRegs] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by
        have hm : ∀ s₁ s₂, (Spec.Ctr.aesContract RISCV64.abi).pre s₁ → (Spec.Ctr.aesContract RISCV64.abi).pre s₂ →
            (Spec.Ctr.aesContract RISCV64.abi).pub s₁ s₂ → (modeRISCV64 AesCtr.ctrMode).pub s₁ s₂ := by
          sig_implies_pub [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeRISCV64, RISCV64.abi, RISCV64.argRegs]
        intro s₁ s₂ h₁ h₂ h
        refine ⟨hm s₁ s₂ h₁ h₂ h, ?_⟩
        sig_pub [Spec.Ctr.aesContract, Spec.Ctr.aesSig, Spec.Ctr.ctrLeak, RISCV64.abi, RISCV64.argRegs] at h
        sig_split h
        exact AesCtr.lo32_of_leak (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _)
          (by assumption)
      sat := by sig_implies_sat [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeRISCV64, RISCV64.abi,
        RISCV64.argRegs] [sat] using sat }

end VG.Proof.AesCtr.RISCV64
