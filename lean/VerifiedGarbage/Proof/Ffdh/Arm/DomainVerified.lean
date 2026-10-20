module

public import VerifiedGarbage.Proof.Ffdh.Arm.DomainCorrect
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainContractCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
import Mathlib.Util.CompileInductive
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.Arm.Target

/-! The native ARMv7 domain check is verified against the shared FFDH API. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

private def domainSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 128 | .r2 => 64 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 0x20 else if a = 0x8001 then 4 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 8448⟩]

theorem domain_sat : ∃ s, (Spec.Ffdh.checkDomainContract abi 128).pre s := by
  sig_implies_sat [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [domainSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using domainSat

theorem domain_verified : Verified target VG.Impl.Ffdh.Arm.Domain.CheckDomain.code
    (Spec.Ffdh.checkDomainContract abi 128) :=
  ⟨domain_correct, domain_contract_ct, domain_sat⟩

end VG.Proof.Ffdh.Arm
