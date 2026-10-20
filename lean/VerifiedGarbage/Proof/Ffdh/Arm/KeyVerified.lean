module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.KeyContractCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
import Mathlib.Util.CompileInductive
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.Arm.Target
public import Init.Core
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Isa

/-! Native ARMv7 key generation is verified against the shared FFDH API. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

private def keySat : State where
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

theorem key_sat : ∃ s, (Spec.Ffdh.generateKeyContract abi 128).pre s := by
  sig_implies_sat [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [keySat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using keySat

theorem key_verified : Verified target VG.Impl.Ffdh.Arm.Domain.GenerateKey.code
    (Spec.Ffdh.generateKeyContract abi 128) :=
  ⟨key_correct, key_contract_ct, key_sat⟩

end VG.Proof.Ffdh.Arm
