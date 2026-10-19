module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86.PrivGeometry
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion

/-! # Decode checked RSA's cdecl arguments into its public buffer geometry -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Proof.Bignum.X86

def privateGeometry (s : State) : PrivGeometry where
  stack := s.gpr .esp - 16 - BitVec.ofNat 32 VG.Impl.Rsa.X86.PrivChecked.frameBytes
  output := arg s 0
  workspace := arg s 18
  sources := fun i => arg s (2 + 2 * i.val)
  length := (arg s 3).toNat
  exponentLength := (arg s 5).toNat
  pLength := (arg s 9).toNat
  qLength := (arg s 11).toNat
  scratchLength := (arg s 19).toNat

def privateBytes (s : State) (i : Fin 8) : List Byte :=
  Spec.Rsa.bytesAt s.mem (byteAddr ((privateGeometry s).sources i)) ((privateGeometry s).sourceLength i)

theorem privateGeometry_stack (s : State) :
    (privateGeometry s).stack = s.gpr .esp - BitVec.ofNat 32 3344 := by
  change s.gpr .esp - 16 - 3328 = _
  rw [BitVec.sub_sub]
  rfl

theorem privateGeometry_stackNat (s : State) (fit : stackBytes ≤ (s.gpr .esp).toNat) :
    (privateGeometry s).stack.toNat = (s.gpr .esp).toNat - 3344 := by
  rw [privateGeometry_stack, sub_toNat (by unfold stackBytes at fit; omega)]

theorem privateGeometry_wholeStack (s : State) (fit : stackBytes ≤ (s.gpr .esp).toNat) :
    (privateGeometry s).wholeStack = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ := by
  unfold PrivGeometry.wholeStack
  rw [privateGeometry_stack, BitVec.sub_sub]
  change (⟨(s.gpr .esp - BitVec.ofNat 32 stackBytes).setWidth 64, stackBytes⟩ : Region) = _
  rw [Taint.sub_setWidth fit]

theorem privateGeometry_arguments (s : State) (fit : stackBytes ≤ (s.gpr .esp).toNat)
    (high : (s.gpr .esp).toNat + 84 ≤ 2 ^ 32) :
    (privateGeometry s).argumentsRegion = ⟨argAddr s 0, 80⟩ := by
  unfold PrivGeometry.argumentsRegion
  rw [privateGeometry_stack]
  change (⟨(s.gpr .esp - BitVec.ofNat 32 3344).setWidth 64 + BitVec.ofNat 64 3348, 80⟩ : Region) = _
  rw [Taint.sub_setWidth (by unfold stackBytes at fit; omega : 3344 ≤ (s.gpr .esp).toNat)]
  have aa : argAddr s 0 = (s.gpr .esp).setWidth 64 + 4 :=
    byteAddr_add (by omega : (s.gpr .esp).toNat + 4 < 2 ^ 32)
  rw [aa, show BitVec.ofNat 64 3348 = BitVec.ofNat 64 3344 + 4 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
end VG.Proof.Rsa.X86.PrivChecked
