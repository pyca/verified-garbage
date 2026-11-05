module
public import VerifiedGarbage.Impl.AesCfb.Arm
public import VerifiedGarbage.Proof.AesCfb.Rounds
public import VerifiedGarbage.Spec.Cfb.Contract
public import VerifiedGarbage.TCB.Arm.Target

import VerifiedGarbage.Proof.AesCbc.Arm.Verified
import VerifiedGarbage.Proof.AesCfb.Arm.Body
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-CFB128 on ARMv7: `Verified`

Correctness and constant time, from the loop AES-CBC's proofs share, a state
satisfying the precondition, and the shared contracts of
`Spec/Cfb/Contract.lean`, with 8 bytes of stack: each call of the block
function pushes its stack argument and `lr`.
-/

@[expose] public section

namespace VG.Proof.AesCfb.Arm

open VG VG.Arm VG.Impl.AesCfb.Arm
open VG.Proof.AesCbc (cts)
open VG.Proof.AesCbc.Arm

theorem encrypt_verified : Verified Arm.target encrypt (Proof.AesCfb.encryptRoundsContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => whole_wp encBody_ok hs) (whole_ct encBody_ok encBody_ct) (by
    sig_implies [Proof.AesCfb.encryptRoundsContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, modeArm, cfbMode, cfb, cts,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat)

theorem decrypt_verified : Verified Arm.target decrypt (Proof.AesCfb.decryptRoundsContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => whole_wp decBody_ok hs) (whole_ct decBody_ok decBody_ct) (by
    sig_implies [Proof.AesCfb.decryptRoundsContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, modeArm, cfbMode, cfb, cts,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat)

end VG.Proof.AesCfb.Arm
