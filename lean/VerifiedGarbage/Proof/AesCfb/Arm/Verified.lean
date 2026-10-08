import VerifiedGarbage.Proof.AesCbc.Arm.Verified
import VerifiedGarbage.Proof.AesCfb.Arm.Body

/-!
# AES-CFB128 on ARMv7: `Verified`

Correctness and constant time, from the loop AES-CBC's proofs share, a state
satisfying the precondition, and the shared contracts of
`Spec/Cfb/Contract.lean`, with 8 bytes of stack: each call of the block
function pushes its stack argument and `lr`.
-/

namespace VG.Proof.AesCfb.Arm

open VG VG.Arm VG.Impl.AesCfb.Arm
open VG.Proof.AesCbc (cts)
open VG.Proof.AesCbc.Arm

theorem encrypt_verified : Verified Arm.target encrypt (Spec.Cfb.aesEncryptContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => whole_wp encBody_ok hs) (whole_ct encBody_ok encBody_ct) (by
    sig_implies [Spec.Cfb.aesEncryptContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, modeArm, cfbMode, cfb, cts,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat)

theorem decrypt_verified : Verified Arm.target decrypt (Spec.Cfb.aesDecryptContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => whole_wp decBody_ok hs) (whole_ct decBody_ok decBody_ct) (by
    sig_implies [Spec.Cfb.aesDecryptContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, modeArm, cfbMode, cfb, cts,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat)

end VG.Proof.AesCfb.Arm
