import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesCbc.Arm.CT

/-!
# AES-CBC on ARMv7: `Verified`

Correctness and constant time, a state satisfying the precondition, and the
shared contracts of `Spec/Cbc/Contract.lean`, with 8 bytes of stack: each
call of a block function pushes its stack argument and `lr`.
-/

namespace VG.Proof.AesCbc.Arm

open VG VG.Arm VG.Impl.AesCbc.Arm

/-- A state satisfying the precondition: the schedule at `0x1000`, 10
rounds, the chaining value at `0x2000`, no blocks at `0x3000` and the scratch
buffer at 0 (the stack arguments, at `0x8000`, are zeros). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0, 2176⟩]

theorem encrypt_verified : Verified Arm.target encrypt (Spec.Cbc.aesEncryptContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => whole_wp encBody_ok hs) (whole_ct encBody_ok encBody_ct) (by
    sig_implies [Spec.Cbc.aesEncryptContract, Spec.Cbc.aesSig, cbcArm, modeArm, cbcMode,
      ciphOf, cbc, cts, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat)

theorem decrypt_verified : Verified Arm.target decrypt (Spec.Cbc.aesDecryptContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => whole_wp decBody_ok hs) (whole_ct decBody_ok decBody_ct) (by
    sig_implies [Spec.Cbc.aesDecryptContract, Spec.Cbc.aesSig, cbcArm, modeArm, cbcMode,
      ciphOf, cbc, cts, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat)

end VG.Proof.AesCbc.Arm
