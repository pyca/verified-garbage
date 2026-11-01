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

/-- A state satisfying the precondition of `vg_dsa_sign`: 1024/160 widths,
a key at `0x2000`, the nonce at `0x4000`, no digest, the output at `0x1000`
and the working space at `0x8000`. -/
def signSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 40 | .r2 => 0x2000 | .r3 => 424 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20000 then 0x80 else if a = 0x20005 then 0x40 else if a = 0x20008 then 20
    else if a = 0x2000d then 0x50 else if a = 0x20015 then 0x80 else if a = 0x20019 then 0x08 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x4000, 20⟩, ⟨0x5000, 0⟩, ⟨0x20000, 28⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x8000, 16384⟩]

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

theorem sign_verified : Verified Arm.target (Entry.operation true) (Spec.Dsa.signContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => sign_correct hs) sign_constantTime (by
    sig_implies [Spec.Dsa.signContract, Spec.Dsa.signSig, signArm, signPre, signRes, signLeak, arg, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
      [signSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using signSat)

theorem verify_verified : Verified Arm.target (Entry.operation false) (Spec.Dsa.verifyContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => verify_correct hs) verify_constantTime (by
    sig_implies [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, verifyArm, verifyPre, verifyRes, verifyLeak, arg,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
      [verifySat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using verifySat)

end VG.Proof.Dsa.Arm
