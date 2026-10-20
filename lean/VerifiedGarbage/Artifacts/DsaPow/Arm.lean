module

import VerifiedGarbage.Proof.Dsa.Arm.PowVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import Batteries.Logic
public import VerifiedGarbage.Impl.Dsa.Arm.Pow
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Dsa.Arm.PowVerified
public import VerifiedGarbage.Proof.Dsa.Arm.ContextCall
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Digit
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.DigitRow
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.MulRow
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ops
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Select
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
public import VerifiedGarbage.Proof.Mont.Arm.Step
public import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Dsa.Arm.ContextCall
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Digit
import VerifiedGarbage.Proof.Mont.Arm.Dyn.DigitRow
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
import VerifiedGarbage.Proof.Mont.Arm.Dyn.MulRow
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ops
import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Select
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Mont.Read

/-! # DSA's exponentiations on ARMv7

One function for each (modulus, exponent) width pair that `vg_dsa_sign` and
`vg_dsa_verify` exponentiate at (`Impl.Dsa.Arm.Core.power`). -/

@[expose] public section

namespace VG.Artifacts.DsaPow.Arm

def helper (n e : Nat)
    (v : Verified Arm.target (Impl.Dsa.Arm.Pow.body n e)
      (Spec.Dsa.ModPow.powContract (Impl.Dsa.Arm.Pow.layout n e) Arm.abi)) : Artifact :=
  (Spec.Dsa.ModPow.powApi (Impl.Dsa.Arm.Pow.layout n e)).artifact Arm.target {
    notes := ["The context's setup and the fixed-schedule square-and-multiply of the DSA functions, \
      on 16-bit digits, with a masked selection. The callee-saved registers reside in the header \
      of `ws`."]
    code := Impl.Dsa.Arm.Pow.body n e
    verified := v }

open Proof.Dsa.Arm.Pow in
def artifacts : List Artifact := [
  helper 16 5 (verified 16 5),
  helper 3 5 (verified 3 5),
  helper 32 5 (verified 32 5),
  helper 32 7 (verified 32 7),
  helper 4 7 (verified 4 7),
  helper 32 8 (verified 32 8),
  helper 4 8 (verified 4 8),
  helper 48 8 (verified 48 8)]

end VG.Artifacts.DsaPow.Arm
