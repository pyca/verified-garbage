module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivContract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The callable ARMv7 checked private RSA operation is verified -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm

def privateSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x21 else
    if a = 0x8004 then 3 else
    if a = 0x8009 then 0x30 else
    if a = 0x800c then 0x40 else
    if a = 0x8011 then 0x31 else
    if a = 0x8014 then 0x20 else
    if a = 0x8019 then 0x32 else
    if a = 0x801c then 0x20 else
    if a = 0x8021 then 0x33 else
    if a = 0x8024 then 0x20 else
    if a = 0x8029 then 0x34 else
    if a = 0x802c then 0x20 else
    if a = 0x8031 then 0x35 else
    if a = 0x8034 then 0x20 else
    if a = 0x8039 then 0x40 else
    if a = 0x803c then 0x20 else
    if a = 0x803d then 4 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 3⟩, ⟨0x3000, 64⟩, ⟨0x3100, 32⟩, ⟨0x3200, 32⟩,
    ⟨0x3300, 32⟩, ⟨0x3400, 32⟩, ⟨0x3500, 32⟩, ⟨0x8000, 64⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem private_contract_sat : ∃ s, (Spec.Rsa.privateCheckedContract abi stackBytes).pre s := by
  sig_implies_sat [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [privateSatState, stackBytes, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
      Spec.Rsa.scratchWords] using privateSatState

theorem code_verified (v : CrtImpl) : Verified target (privCode v) (Spec.Rsa.privateCheckedContract abi stackBytes) :=
  ⟨private_contract_correct v, private_contract_ct v, private_contract_sat⟩
end VG.Proof.Rsa.Arm
