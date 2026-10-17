module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivEntryReady
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Decode the native AAPCS private-key arguments into a public layout -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

def privateGeometry (s : State) : PrivGeometry where
  stack := s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes
  output := s.gpr .r0
  workspace := stackArg s 14
  sources := fun i => match i.val with
    | 0 => s.gpr .r2 | 1 => stackArg s 0 | 2 => stackArg s 2 | 3 => stackArg s 4
    | 4 => stackArg s 6 | 5 => stackArg s 8 | 6 => stackArg s 10 | _ => stackArg s 12
  length := (s.gpr .r3).toNat
  exponentLength := (stackArg s 1).toNat
  pLength := (stackArg s 5).toNat
  qLength := (stackArg s 7).toNat
  scratchLength := (stackArg s 15).toNat

def privateBytes (s : State) (i : Fin 8) : List Byte :=
  Spec.Rsa.bytesAt s.mem (State.addr ((privateGeometry s).sources i)) ((privateGeometry s).sourceLength i)

theorem privateGeometry_stack (s : State) :
    (privateGeometry s).stack = s.sp - BitVec.ofNat 32 (56 + frameBytes) := by
  change s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes = _
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]

theorem privateGeometry_stackNat (s : State) (fit : stackBytes ≤ s.sp.toNat) :
    (privateGeometry s).stack.toNat = s.sp.toNat - (56 + frameBytes) := by
  rw [privateGeometry_stack, FrameStack.sub_toNat' (by simp only [stackBytes, frameBytes] at *; omega)]

theorem privateGeometry_wholeStack (s : State) (fit : stackBytes ≤ s.sp.toNat) :
    (privateGeometry s).wholeStack = ⟨State.addr s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩ := by
  unfold PrivGeometry.wholeStack
  rw [privateGeometry_stack, BitVec.sub_sub, ← BitVec.ofNat_add]
  change (⟨State.addr (s.sp - BitVec.ofNat 32 stackBytes), stackBytes⟩ : Region) = _
  rw [FrameStack.addr_sub' fit]

theorem privateGeometry_arguments (s : State) (fit : stackBytes ≤ s.sp.toNat) :
    (privateGeometry s).argumentsRegion = ⟨State.addr s.sp, 64⟩ := by
  unfold PrivGeometry.argumentsRegion
  rw [privateGeometry_stack, FrameStack.addr_sub' (by simp only [stackBytes, frameBytes] at *; omega)]
  change (⟨State.addr s.sp - BitVec.ofNat 64 (56 + frameBytes) + BitVec.ofNat 64 (56 + frameBytes), 64⟩ : Region) = _
  rw [BitVec.sub_add_cancel]
end VG.Proof.Rsa.Arm
