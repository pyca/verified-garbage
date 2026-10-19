module
public import Batteries.Logic
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Impl.AesCfb8.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Cfb8.Contract
public import VerifiedGarbage.TCB.Arm.Target

import VerifiedGarbage.Proof.AesCbc.Arm.Verified
import VerifiedGarbage.Proof.AesCfb8.Arm.CT
import VerifiedGarbage.Proof.AesCbc.Arm.CT

/-!
# AES-CFB8 on ARMv7: `Verified`

Correctness and constant time, AES-CBC's state satisfying the
precondition, and the shared contracts of `Spec/Cfb8/Contract.lean`, with 8
bytes of stack: each call of the block
function pushes its stack argument and `lr`.
-/

@[expose] public section

namespace VG.Proof.AesCfb8.Arm

open VG VG.Arm VG.Impl.AesCfb8.Arm
open VG.Proof.AesCbc.Arm (sat)

theorem encrypt_verified : Verified Arm.target encrypt (Spec.Cfb8.aesEncryptContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => whole_wp encBody_ok hs) (whole_ct encBody_ok encBody_ct) (by
    sig_implies [Spec.Cfb8.aesEncryptContract, Spec.Cfb8.aesSig, cfb8Arm, cfb8, cts, inK,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat)

theorem decrypt_verified : Verified Arm.target decrypt (Spec.Cfb8.aesDecryptContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => whole_wp decBody_ok hs) (whole_ct decBody_ok decBody_ct) (by
    sig_implies [Spec.Cfb8.aesDecryptContract, Spec.Cfb8.aesSig, cfb8Arm, cfb8, cts, inK,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat)

end VG.Proof.AesCfb8.Arm
