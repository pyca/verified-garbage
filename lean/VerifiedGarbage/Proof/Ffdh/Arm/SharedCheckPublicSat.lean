module

import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic

/-! The enlarged public-check signature remains satisfiable. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

private def sharedPublicSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 128 | .r2 => 64 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 64 else if a = 0x8005 then 0x30 else
    if a = 0x8008 then 0x20 else if a = 0x8009 then 4 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩, ⟨0x8000, 12⟩]
  wr := [⟨0x3000, 8448⟩]

theorem sharedCheckPublic_sat : ∃ s, (Spec.Ffdh.checkPublicContract abi 176).pre s := by
  sig_implies_sat [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [sharedPublicSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using sharedPublicSat

end VG.Proof.Ffdh.Arm
