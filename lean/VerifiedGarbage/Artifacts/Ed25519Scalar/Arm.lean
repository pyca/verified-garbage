module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarVerified
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Spill

/-! Baseline ARMv7 Ed25519 primitive with register saves in the reviewed scratch buffer. -/

@[expose] public section

namespace VG.Artifacts.Ed25519Scalar.Arm

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarReduceApi with
    target := Arm.target
    doc := Spec.Ed25519.scalarReduceApi.doc (notes := ["Processes all 512 input bits with \
      sixteen 16-bit limbs, subtracting the subgroup order and selecting with a mask. \
      Callee-saved registers are saved in the first 32 bytes of `scratch`."])
    code := Impl.Ed25519.Arm.scalarReduce
    contract := Spec.Ed25519.scalarReduceContract Arm.abi
    verified := Proof.Ed25519.Arm.scalarReduce_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519Scalar.Arm
