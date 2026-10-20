module

public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateCorrect
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateContractCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
import Mathlib.Util.CompileInductive
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.Arm.Target

/-! Native ARMv7 imported private-key validation is verified against the shared FFDH API. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

private def privateSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 128 | .r2 => 64 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 64 else if a = 0x8005 then 0x21 else if a = 0x8008 then 1 else
    if a = 0x800d then 0x30 else if a = 0x8010 then 0x20 else if a = 0x8011 then 4 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x8000, 20⟩]
  wr := [⟨0x3000, 8448⟩]

theorem private_sat : ∃ s, (Spec.Ffdh.checkPrivateContract abi 128).pre s := by
  sig_implies_sat [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [privateSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using privateSat

theorem private_verified : Verified target VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code
    (Spec.Ffdh.checkPrivateContract abi 128) :=
  ⟨private_correct, private_contract_ct, private_sat⟩

end VG.Proof.Ffdh.Arm
