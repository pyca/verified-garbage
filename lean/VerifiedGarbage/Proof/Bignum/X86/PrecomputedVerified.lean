module
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn
public import VerifiedGarbage.Spec.Weierstrass.Point
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.X86.Target

import VerifiedGarbage.Proof.Bignum.X86.PrecomputedOperationTiming
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedObservations
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedCorrect
import VerifiedGarbage.Proof.Bignum.Words

/-! # Complete i686 certificate for checked public RSA -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86

theorem precomputedConstantTime : ConstantTime isa (Spec.Rsa.publicPrecomputedCheckedContract abi 20).pre
    (Spec.Rsa.publicPrecomputedCheckedContract abi 20).pub PrecomputedFn.code := by
  intro s t tr ur sf tf S T H E F
  have Args := precomputedArguments H
  have Key := precomputedKeyBytes H
  exact precomputedOperation_trace (precomputedABI_of S) (precomputedABI_of T) Args.2 Args.1 Key.1 Key.2 E F

/-- Disjoint 512-bit buffers; the zero-valued packed key is rejected at runtime. -/
def precomputedSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16 else if a = 0x20008 then 64 else if a = 0x2000d then 32
    else if a = 0x20010 then 16 else if a = 0x20015 then 48 else if a = 0x20018 then 1
    else if a = 0x2001d then 64 else if a = 0x20020 then 64 else if a = 0x20025 then 128
    else if a = 0x20028 then 128 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 1024⟩, ⟨0x20004, 40⟩]

theorem precomputedSatisfiable : ∃ s, (Spec.Rsa.publicPrecomputedCheckedContract abi 20).pre s := by
  have a0 : arg precomputedSatState 0 = 4096 := by decide
  have a1 : arg precomputedSatState 1 = 64 := by decide
  have a2 : arg precomputedSatState 2 = 8192 := by decide
  have a3 : arg precomputedSatState 3 = 16 := by decide
  have a4 : arg precomputedSatState 4 = 12288 := by decide
  have a5 : arg precomputedSatState 5 = 1 := by decide
  have a6 : arg precomputedSatState 6 = 16384 := by decide
  have a7 : arg precomputedSatState 7 = 64 := by decide
  have a8 : arg precomputedSatState 8 = 32768 := by decide
  have a9 : arg precomputedSatState 9 = 128 := by decide
  have e : argAddr precomputedSatState 0 = 0x20004 := by decide
  have esp : precomputedSatState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp, precomputedSatState, Spec.Rsa.lenValid,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords] using precomputedSatState

theorem precomputed_verified : Verified target PrecomputedFn.code (Spec.Rsa.publicPrecomputedCheckedContract abi 20) :=
  ⟨precomputedCorrect, precomputedConstantTime, precomputedSatisfiable⟩

end VG.Proof.Bignum.X86
