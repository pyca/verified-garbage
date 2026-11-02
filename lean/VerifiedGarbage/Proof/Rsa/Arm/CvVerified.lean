module

public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
import VerifiedGarbage.Proof.Rsa.Arm.CvCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Rsa.Arm.CvCorrect

/-! # `vg_rsa_crt_values` on ARMv7 is verified against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Impl.Rsa.Arm.CrtValues

/-- A 64-byte modulus, one-byte factors, exponent and outputs, the working
space at `0x4000`, and the stack arguments at `0x8000`. -/
def cvSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x1200 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x11 else if a = 0x8004 then 1 else if a = 0x8009 then 0x20
    else if a = 0x800C then 0x40 else if a = 0x8011 then 0x30 else if a = 0x8014 then 1
    else if a = 0x8019 then 0x31 else if a = 0x801C then 1 else if a = 0x8021 then 0x32
    else if a = 0x8024 then 1 else if a = 0x8029 then 0x40 else if a = 0x802C then 0x20
    else if a = 0x802D then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x8000, 48⟩]
  wr := [⟨0x1000, 1⟩, ⟨0x1200, 1⟩, ⟨0x1100, 1⟩, ⟨0x4000, 8448⟩]

theorem cv_contract_sat : ∃ s, (Spec.Rsa.crtValuesContract abi 0).pre s := by
  sig_implies_sat [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr]
    [cvSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords]
    using cvSatState

/-- `vg_rsa_crt_values`. -/
theorem crt_values_verified [VG.Proof.Rsa.Arm.Keys.InvLaw] : Verified target code (Spec.Rsa.crtValuesContract abi 0) :=
  ⟨cv_contract_correct, cv_contract_ct, cv_contract_sat⟩

end VG.Proof.Rsa.Arm.CrtValues
