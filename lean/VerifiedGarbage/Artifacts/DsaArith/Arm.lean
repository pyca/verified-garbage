module

import VerifiedGarbage.Proof.Dsa.Arm.ArithVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.Arm.Arith
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.Dsa.Arm.Core

/-! # DSA's reductions and products on ARMv7

One reduction for each width of q, and one product for each width of p and
q, that `vg_dsa_sign` and `vg_dsa_verify` use (`Impl.Dsa.Arm.Core.reduce`,
`Impl.Dsa.Arm.Core.productMod`). -/

@[expose] public section

namespace VG.Artifacts.DsaArith.Arm

def reduceHelper (n : Nat)
    (v : Verified Arm.target (Impl.Dsa.Arm.Arith.reduceBody n)
      (Spec.Dsa.ModArith.reduceContract (Impl.Dsa.Arm.Arith.reduceLayout n) Arm.abi)) : Artifact :=
  (Spec.Dsa.ModArith.reduceApi (Impl.Dsa.Arm.Arith.reduceLayout n)).artifact Arm.target {
    notes := ["The context's setup of the DSA functions, then the bytes reduced one at a time: \
      eight modular doublings and an addition each, on 16-bit digits. The callee-saved registers \
      and the bytes' length reside in the header of `ws`."]
    code := Impl.Dsa.Arm.Arith.reduceBody n
    verified := v }

def mulHelper (n : Nat)
    (v : Verified Arm.target (Impl.Dsa.Arm.Arith.mulBody n)
      (Spec.Dsa.ModArith.mulContract (Impl.Dsa.Arm.Arith.mulLayout n) Arm.abi)) : Artifact :=
  (Spec.Dsa.ModArith.mulApi (Impl.Dsa.Arm.Arith.mulLayout n)).artifact Arm.target {
    notes := ["The context's setup of the DSA functions, then two Montgomery multiplications on \
      16-bit digits: by `R² mod m`, then by the other operand. The callee-saved registers reside \
      in the header of `ws`."]
    code := Impl.Dsa.Arm.Arith.mulBody n
    verified := v }

open Proof.Dsa.Arm.Pow in
def artifacts : List Artifact := [
  reduceHelper 3 (reduceVerified 3),
  reduceHelper 4 (reduceVerified 4),
  mulHelper 3 (mulVerified 3),
  mulHelper 4 (mulVerified 4),
  mulHelper 16 (mulVerified 16),
  mulHelper 32 (mulVerified 32),
  mulHelper 48 (mulVerified 48)]

end VG.Artifacts.DsaArith.Arm
