module

import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveContractCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
import Mathlib.Util.CompileInductive
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
meta import VerifiedGarbage.TCB.Arm.Target
public import Init.Core
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedDerivePrograms
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract

/-! The native ARMv7 derivation of an imported scalar's public value is verified against the
shared FFDH API. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm

private def deriveSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 128 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 64 else if a = 0x8005 then 0x30 else if a = 0x8008 then 1 else
    if a = 0x800d then 0x40 else if a = 0x8010 then 0x20 else if a = 0x8011 then 4 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x8000, 20⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem sat : ∃ s, (Spec.Ffdh.derivePublicContract abi 176).pre s := by
  sig_implies_sat [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, Spec.Ffdh.pLenValid,
    Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [deriveSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using deriveSat

theorem verified (backend : VG.Proof.Bignum.Arm.MontBackend) : Verified target (code backend)
    (Spec.Ffdh.derivePublicContract abi 176) :=
  ⟨correct backend, contract_ct backend, sat⟩

end VG.Proof.Ffdh.Arm.SharedDerive
