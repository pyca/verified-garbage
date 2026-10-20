module

public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeCorrect
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeContractCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
import Mathlib.Util.CompileInductive
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.Arm.Target

/-! Native ARMv7 shared-secret computation is verified against the shared FFDH API. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

private def exchangeSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 128 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 64 else if a = 0x8005 then 0x30 else if a = 0x8008 then 1 else
    if a = 0x800d then 0x31 else if a = 0x8010 then 64 else if a = 0x8015 then 0x40 else
    if a = 0x8018 then 0x20 else if a = 0x8019 then 4 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x3100, 64⟩, ⟨0x8000, 28⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem exchange_sat : ∃ s, (Spec.Ffdh.exchangeContract abi 128).pre s := by
  sig_implies_sat [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, Spec.Ffdh.pLenValid,
    Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [exchangeSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using exchangeSat

theorem exchange_verified : Verified target VG.Impl.Ffdh.Arm.Domain.Exchange.code
    (Spec.Ffdh.exchangeContract abi 128) :=
  ⟨exchange_correct, exchange_contract_ct, exchange_sat⟩

end VG.Proof.Ffdh.Arm
