module
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.TCB.X86.Target

import VerifiedGarbage.Proof.Rsa.X86.CvOperationTiming
import VerifiedGarbage.Proof.Rsa.X86.CvCorrect

/-! # Complete i686 certificate for CRT parameter calculation -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86
open VG.Impl.Rsa.X86.CrtValuesRt (code)

/-- Disjoint 512-bit buffers with the contract's full scratch allowance. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 32
    else if a = 0x2000d then 32
    else if a = 0x20010 then 32
    else if a = 0x20015 then 48
    else if a = 0x20018 then 32
    else if a = 0x2001d then 64
    else if a = 0x20020 then 64
    else if a = 0x20025 then 80
    else if a = 0x20028 then 32
    else if a = 0x2002d then 96
    else if a = 0x20030 then 32
    else if a = 0x20035 then 112
    else if a = 0x20038 then 64
    else if a = 0x2003e then 1
    else if a = 0x20040 then 32
    else if a = 0x20041 then 4 else 0
  rd := [⟨0x4000, 64⟩, ⟨0x5000, 32⟩, ⟨0x6000, 32⟩, ⟨0x7000, 64⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x10000, 8448⟩, ⟨0x20004, 64⟩]

theorem satisfiable : ∃ s, (Spec.Rsa.crtValuesContract abi 20).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 32 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 32 := by decide
  have a4 : arg satState 4 = 12288 := by decide
  have a5 : arg satState 5 = 32 := by decide
  have a6 : arg satState 6 = 16384 := by decide
  have a7 : arg satState 7 = 64 := by decide
  have a8 : arg satState 8 = 20480 := by decide
  have a9 : arg satState 9 = 32 := by decide
  have a10 : arg satState 10 = 24576 := by decide
  have a11 : arg satState 11 = 32 := by decide
  have a12 : arg satState 12 = 28672 := by decide
  have a13 : arg satState 13 = 64 := by decide
  have a14 : arg satState 14 = 65536 := by decide
  have a15 : arg satState 15 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, satState, Spec.Rsa.lenValid, Spec.Rsa.scratchWords] using satState

theorem verified : Verified target code (Spec.Rsa.crtValuesContract abi 20) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Rsa.X86.CrtValues
