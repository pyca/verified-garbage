module

import VerifiedGarbage.Proof.AesXts.Arm.Unit.CT
public import VerifiedGarbage.Proof.Framework.Contract
public import Batteries.Logic
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.AesXts.Arm.Unit.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.AesXts.Arm.Unit.Dec
import VerifiedGarbage.Proof.AesXts.Arm.Verified

/-!
# XTS-AES of data units on ARMv7: `Verified`

Correctness (`encrypt_wp`, `decrypt_wp`) and constant time (`encrypt_ct`,
`decrypt_ct`), a state satisfying the precondition (`unitSat`), and the
shared contracts of `Spec/Xts/Contract.lean`, with 16 bytes of stack: the
frame of a whole-block function's stack arguments, and its frames of its
block functions' stack argument.
-/

@[expose] public section

namespace VG.Proof.AesXts.Arm.Unit

open VG VG.Arm VG.Impl.AesXts.ArmUnit

theorem encrypt_correct (s : State) (hs : (unitArm true).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (unitArm true).post s s' :=
  encrypt_wp (UPre.of hs)

theorem decrypt_correct (s : State) (hs : (unitArm false).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (unitArm false).post s s' :=
  decrypt_wp (UPre.of hs)

/-- A state satisfying the precondition: AES-128, a data unit of one block
at 0, and the scratch buffer at `0x100` (the stack arguments, at `0x8000`). -/
def unitSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 10 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8004 then 16 else if a = 0x8009 then 1 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 240⟩, ⟨0x3000, 16⟩, ⟨0x8000, 12⟩]
  wr := [⟨0, 16⟩, ⟨0x100, 2432⟩]

theorem encrypt_verified : Verified Arm.target encrypt (Spec.Xts.aesEncryptUnitContract Arm.abi 16) :=
  Verified.of_correct encrypt_correct encrypt_ct (by
    sig_implies [Spec.Xts.aesEncryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesEncryptUnitPost, unitArm, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, Sa, Da, schR, tschR, iR,
      dataR, scrR, argsR, stkR, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [unitSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using unitSat)

theorem decrypt_verified : Verified Arm.target decrypt (Spec.Xts.aesDecryptUnitContract Arm.abi 16) :=
  Verified.of_correct decrypt_correct decrypt_ct (by
    sig_implies [Spec.Xts.aesDecryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesDecryptUnitPost, unitArm, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, Sa, Da, schR, tschR, iR,
      dataR, scrR, argsR, stkR, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [unitSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using unitSat)

end VG.Proof.AesXts.Arm.Unit
