module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.Contract
meta import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.Ffdh.SievedContract

/-! The public ARMv7 candidate contract has a concrete allowed call. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

private def candidateSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x1100 | .r3 => 512 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 2 else if a = 0x8005 then 0x20 else if a = 0x800d then 0x30 else
    if a = 0x8010 then 0x20 else if a = 0x8011 then 4 else 0
  rd := [⟨0x2000, 0⟩, ⟨0x8000, 20⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x3000, 8448⟩]

theorem candidate_sat : ∃ s, (Proof.Ffdh.sievedParameterCandidateContract abi 184).pre s := by
  sig_implies_sat [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
    [candidateSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using candidateSat

end VG.Proof.Ffdh.Arm.ParameterCandidate
