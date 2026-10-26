module

import VerifiedGarbage.Proof.Bignum.Arm.PdContract
public import VerifiedGarbage.Proof.Framework.Contract
public import Batteries.Logic
import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Impl.Bignum.Arm.PdFn
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Bignum.Words

/-! # ARMv7 checked public RSA is verified against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

/-- Separate 64-byte buffers, a one-byte exponent, and native stack arguments. -/
def pdSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 16 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else if a = 0x8004 then 1 else
    if a = 0x8009 then 0x31 else if a = 0x800c then 64 else
    if a = 0x8011 then 0x40 else if a = 0x8014 then 0x20 else if a = 0x8015 then 4 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x3100, 64⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem pd_contract_sat : ∃ s, (Spec.Rsa.publicPrecomputedCheckedContract abi 56).pre s := by
  sig_implies_sat [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [pdSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
      Spec.Rsa.scratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using pdSatState

theorem pd_verified : Verified target PdFn.code (Spec.Rsa.publicPrecomputedCheckedContract abi 56) :=
  ⟨pd_contract_correct, pd_contract_ct, pd_contract_sat⟩

end VG.Proof.Bignum.Arm
