module
public import VerifiedGarbage.Impl.AesOfb.Arm
public import VerifiedGarbage.Spec.Ofb.Contract
public import VerifiedGarbage.TCB.Arm.Target

import VerifiedGarbage.Proof.AesCbc.Arm.Verified
import VerifiedGarbage.Proof.AesOfb.Arm.Body
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-OFB on ARMv7: `Verified`

Correctness and constant time, from the loop AES-CBC's proofs share, a state
satisfying the precondition, and the shared contract of
`Spec/Ofb/Contract.lean`, with 8 bytes of stack: each call of the block
function pushes its stack argument and `lr`.
-/

@[expose] public section

namespace VG.Proof.AesOfb.Arm

open VG VG.Arm VG.Impl.AesOfb.Arm
open VG.Proof.AesCbc.Arm

theorem crypt_verified : Verified Arm.target crypt (Spec.Ofb.aesContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => whole_wp body_ok hs) (whole_ct body_ok body_ct)
    { pre := by sig_implies_pre [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeArm, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      -- `ofbMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeArm, ofbMode, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        sig_reduce [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeArm, ofbMode, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        sig_simp [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeArm, ofbMode, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeArm, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by sig_implies_sat [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeArm, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat }

end VG.Proof.AesOfb.Arm
