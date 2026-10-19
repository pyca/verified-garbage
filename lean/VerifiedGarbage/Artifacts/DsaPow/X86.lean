module

import VerifiedGarbage.Proof.Dsa.X86.PowVerified
import VerifiedGarbage.Proof.Dsa.X86.PowCall
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.Dsa.X86.Core
import VerifiedGarbage.Proof.Dsa.X86.PowABI

/-! # DSA's exponentiations on baseline i686

One function for each (modulus, exponent) width pair that `vg_dsa_sign` and
`vg_dsa_verify` exponentiate at (`Impl.Dsa.X86.Core.power`). -/

@[expose] public section

namespace VG.Artifacts.DsaPow.X86

def helper (n e : Nat)
    (v : Verified X86.target (Impl.Dsa.X86.Pow.body n e)
      (Spec.Dsa.ModPow.powContract (Impl.Dsa.X86.Pow.layout n e) X86.abi 20)) : Artifact :=
  (Spec.Dsa.ModPow.powApi (Impl.Dsa.X86.Pow.layout n e)).artifact X86.target {
    notes := ["The context's setup and the fixed-schedule square-and-multiply of the DSA functions, \
      on 32-bit words, with a masked selection. The callee-saved registers reside in the header \
      of `ws`."]
    code := Impl.Dsa.X86.Pow.body n e
    verified := v
    stack := 20
    spSafe := Code.all_of_allInstrs (Proof.Dsa.X86.Pow.body_spSafe n e) }

open Proof.Dsa.X86.Pow in
def artifacts : List Artifact := [
  helper 16 5 (verified 16 5),
  helper 3 5 (verified 3 5),
  helper 32 5 (verified 32 5),
  helper 32 7 (verified 32 7),
  helper 4 7 (verified 4 7),
  helper 32 8 (verified 32 8),
  helper 4 8 (verified 4 8),
  helper 48 8 (verified 48 8)]

end VG.Artifacts.DsaPow.X86
