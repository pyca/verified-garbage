module

import VerifiedGarbage.Proof.Dsa.Arm.VerifyCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.Arm.Entry
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Dsa.Arm.SignCT
import VerifiedGarbage.Proof.Dsa.Arm.VerifyCorrect
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect

/-!
# DSA on 32-bit ARM: `Verified`

Untrusted: everything here is checked by Lean. Correctness
(`SignCorrect.lean`, `VerifyCorrect.lean`), constant time (`SignCT.lean`,
`VerifyCT.lean`), and states satisfying the shared contracts of
`Spec/Dsa/SignVerify.lean`, which `signArm` and `verifyArm` restate. Neither
function uses the stack beyond its arguments.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Dsa.Arm

/-- A state satisfying the precondition of `vg_dsa_verify`: as `signSat`,
with the signature at `0x4000`. -/
def verifySat : State where
  gpr r := match r with | .r0 => 0x2000 | .r1 => 404 | .r2 => 128 | .r3 => 20 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20001 then 0x40 else if a = 0x20004 then 40 else if a = 0x20009 then 0x50
    else if a = 0x20011 then 0x80 else if a = 0x20015 then 0x08 else 0
  rd := [⟨0x2000, 404⟩, ⟨0x4000, 40⟩, ⟨0x5000, 0⟩, ⟨0x20000, 24⟩]
  wr := [⟨0x8000, 16384⟩]

end VG.Proof.Dsa.Arm
