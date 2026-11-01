module
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.X86.Target

import VerifiedGarbage.Proof.Bignum.X86.PrecomputeOperationTiming
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeObservations
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeCorrect
import VerifiedGarbage.Proof.Bignum.Words

/-! # Complete i686 certificate for public RSA precomputation -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86

theorem precomputeConstantTime : ConstantTime isa (Spec.Rsa.publicPrecomputeContract abi 96).pre
    (Spec.Rsa.publicPrecomputeContract abi 96).pub PrecomputeFn.code := by
  intro s t tr ur sf tf S T H E F
  have Args := precomputeArguments H
  exact precomputeOperation_trace (precomputeABI_of S) (precomputeABI_of T) Args.2 Args.1
    (precomputeModulusBytes H) E F

/-- Disjoint buffers for a 512-bit modulus, rejected because its bytes are zero. -/
def precomputeSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16 else if a = 0x20008 then 16 else if a = 0x2000d then 32
    else if a = 0x20010 then 64 else if a = 0x20015 then 128 else if a = 0x20018 then 128 else 0
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x8000, 1024⟩, ⟨0x20004, 24⟩]

theorem precomputeSatisfiable : ∃ s, (Spec.Rsa.publicPrecomputeContract abi 96).pre s := by
  have a0 : arg precomputeSatState 0 = 4096 := by decide
  have a1 : arg precomputeSatState 1 = 16 := by decide
  have a2 : arg precomputeSatState 2 = 8192 := by decide
  have a3 : arg precomputeSatState 3 = 64 := by decide
  have a4 : arg precomputeSatState 4 = 32768 := by decide
  have a5 : arg precomputeSatState 5 = 128 := by decide
  have e : argAddr precomputeSatState 0 = 0x20004 := by decide
  have esp : precomputeSatState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, e, esp, precomputeSatState, Spec.Rsa.lenValid,
      Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using precomputeSatState

theorem precompute_verified : Verified target PrecomputeFn.code (Spec.Rsa.publicPrecomputeContract abi 96) :=
  ⟨precomputeCorrect, precomputeConstantTime, precomputeSatisfiable⟩

end VG.Proof.Bignum.X86
