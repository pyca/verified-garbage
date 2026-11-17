module
public import VerifiedGarbage.Impl.AesCtr.Arm
public import VerifiedGarbage.Proof.AesCtr.Rounds
public import VerifiedGarbage.Spec.Ctr.Contract
public import VerifiedGarbage.TCB.Arm.Target

import VerifiedGarbage.Proof.AesCbc.Arm.Verified
import VerifiedGarbage.Proof.AesCtr.Arm.Body
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.Cmac.Spec

/-!
# AES-CTR on ARMv7: `Verified`

Correctness and constant time, from `crypt_wp` and `crypt_ct`, a state
satisfying the precondition, and the shared contract of
`Spec/Ctr/Contract.lean`, with 8 bytes of stack (each call of
`vg_aes_ctr32` pushes its two stack arguments), whose `leak` (the counter
block's last four bytes) gives the agreement on the last 32 bits of the
counter block `crypt_ct` assumes (`ctrPub`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.Arm

open VG VG.Arm VG.Impl.AesCtr.Arm
open VG.Proof.AesCbc.Arm

theorem crypt_verified : Verified Arm.target crypt (Proof.AesCtr.roundsContract Arm.abi 8) := by
  have hc : ∀ s, (modeArm AesCtr.ctrMode).pre s →
      ∃ t s', Exec isa crypt s t s' ∧ abiPreserved s s' ∧ (modeArm AesCtr.ctrMode).post s s' :=
    fun _ hs => crypt_wp hs
  exact Verified.of_correct (k := { modeArm AesCtr.ctrMode with pub := ctrPub }) hc crypt_ct
    { pre := by sig_implies_pre [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeArm, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      -- `ctrMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeArm, AesCtr.ctrMode, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        sig_reduce [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeArm, AesCtr.ctrMode, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        sig_simp [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeArm, AesCtr.ctrMode, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by
        have hm : ∀ s₁ s₂, (Proof.AesCtr.roundsContract Arm.abi 8).pre s₁ →
            (Proof.AesCtr.roundsContract Arm.abi 8).pre s₂ →
            (Proof.AesCtr.roundsContract Arm.abi 8).pub s₁ s₂ → (modeArm AesCtr.ctrMode).pub s₁ s₂ := by
          sig_implies_pub [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeArm, Arm.abi,
            Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        intro s₁ s₂ h₁ h₂ h
        refine ⟨hm s₁ s₂ h₁ h₂ h, ?_⟩
        sig_pub [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, Spec.Ctr.ctrLeak, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        sig_split h
        exact AesCtr.lo32_of_leak (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _)
          (by assumption)
      sat := by sig_implies_sat [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeArm, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat }

end VG.Proof.AesCtr.Arm
