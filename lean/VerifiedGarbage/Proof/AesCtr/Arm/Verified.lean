import VerifiedGarbage.Proof.AesCbc.Arm.Verified
import VerifiedGarbage.Proof.AesCtr.Arm.Body

/-!
# AES-CTR on ARMv7: `Verified`

Correctness and constant time, from the loop AES-CBC's proofs share, a state
satisfying the precondition, and the shared contract of
`Spec/Ctr/Contract.lean`, with 8 bytes of stack: each call of the block
function pushes its stack argument and `lr`.
-/

namespace VG.Proof.AesCtr.Arm

open VG VG.Arm VG.Impl.AesCtr.Arm
open VG.Proof.AesCbc.Arm

theorem crypt_verified : Verified Arm.target crypt (Spec.Ctr.aesContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => whole_wp body_ok hs) (whole_ct body_ok body_ct)
    { pre := by sig_implies_pre [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeArm, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      -- `ctrMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeArm, AesCtr.ctrMode, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        sig_reduce [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeArm, AesCtr.ctrMode, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        sig_simp [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeArm, AesCtr.ctrMode, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeArm, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by sig_implies_sat [Spec.Ctr.aesContract, Spec.Ctr.aesSig, modeArm, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat }

end VG.Proof.AesCtr.Arm
