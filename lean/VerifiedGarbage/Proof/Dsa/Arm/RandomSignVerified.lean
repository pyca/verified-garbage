module

import VerifiedGarbage.Proof.Dsa.Arm.RandomSignCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.Arm.Entry
public import VerifiedGarbage.Impl.Dsa.Arm.RandomSign
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Dsa.Arm.RandomSignCorrect

/-! # The 32-bit ARM randomized signer meets its contract -/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.RandomSign

/-- A 1024/160 call with an empty tape: the output at `0x1000`, `used` at
`0x7000`, the key at `0x2000` and the working space at `0x8000`. -/
def randomSignSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 40 | .r2 => 0x7000 | .r3 => 0x2000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20000 then 0xa8 else if a = 0x20001 then 1 else if a = 0x20004 then 0x80
    else if a = 0x20008 then 20 else if a = 0x2000d then 0x50 else if a = 0x20015 then 0x60
    else if a = 0x2001d then 0x80 else if a = 0x20020 then 0x40 else if a = 0x20021 then 0x08 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x20000, 36⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x7000, 8⟩, ⟨0x8000, 16896⟩]

theorem randomSign_satisfiable : ∃ s, (Spec.Dsa.randomSignContract Arm.abi 144).pre s := by
  sig_implies_sat [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
    [randomSignSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using randomSignSat

theorem randomSign_verified (name : String) :
    Verified Arm.target (code name (Entry.operation true)) (Spec.Dsa.randomSignContract Arm.abi 144) :=
  ⟨randomSign_correct name, randomSign_constantTime name, randomSign_satisfiable⟩

/-- The randomized signer, calling the registered `vg_dsa_sign`. -/
theorem randomSigning_verified : Verified Arm.target (code "vg_dsa_sign" (Entry.operation true))
    (Spec.Dsa.randomSignContract Arm.abi 144) :=
  randomSign_verified _

end VG.Proof.Dsa.Arm
