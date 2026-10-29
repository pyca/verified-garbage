module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateContractCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.Arm.Target
public import Init.Core
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Isa

/-! Native ARMv7 key generation is verified against the shared FFDH API. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

private def keyGenerateSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x1100 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x20 else if a = 0x8004 then 128 else if a = 0x8008 then 64 else
    if a = 0x800d then 0x21 else if a = 0x8010 then 64 else if a = 0x8015 then 0x30 else
    if a = 0x8018 then 0x20 else if a = 0x8019 then 4 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x2100, 64⟩, ⟨0x8000, 28⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x3000, 8448⟩]

theorem keyGenerate_sat : ∃ s, (Spec.Ffdh.generateKeyContract abi 176).pre s := by
  sig_implies_sat [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [keyGenerateSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using keyGenerateSat

theorem keyGenerate_verified (prepare tail : Prog isa) (prep : KeyPrepareLaw prepare) (law : KeyTailLaw tail) :
    Verified target (VG.Impl.Ffdh.Arm.KeyGenerate.code prepare tail)
    (Spec.Ffdh.generateKeyContract abi 176) :=
  ⟨keyGenerate_correct prepare tail prep law, keyGenerate_contract_ct prepare tail prep law, keyGenerate_sat⟩

end VG.Proof.Ffdh.Arm
