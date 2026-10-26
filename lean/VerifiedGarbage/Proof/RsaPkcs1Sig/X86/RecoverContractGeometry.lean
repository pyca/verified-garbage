module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverGeometry
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Weierstrass

/-! # Decode checked RSA's cdecl arguments into its public buffer geometry -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86

def recoverGeometry (s : State) : Geometry where
  stack := s.gpr .esp - 16 - BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes
  output := arg s 0
  outputLength := (arg s 1).toNat
  workspace := arg s 9
  sources := fun i => arg s (match i.val with | 0 => 2 | 1 => 4 | 2 => 7 | _ => 11)
  length := (arg s 3).toNat
  hash := arg s 6
  exponentLength := (arg s 5).toNat
  signatureLength := (arg s 8).toNat
  preLength := (arg s 12).toNat
  scratchLength := (arg s 10).toNat

def recoverBytes (s : State) (i : Fin 4) : List Byte :=
  Spec.Rsa.bytesAt s.mem (byteAddr ((recoverGeometry s).sources i)) ((recoverGeometry s).sourceLength i)

theorem recoverGeometry_stack (s : State) :
    (recoverGeometry s).stack = s.gpr .esp - BitVec.ofNat 32 2128 := by
  change s.gpr .esp - 16 - 2112 = _
  rw [BitVec.sub_sub]
  rfl

theorem recoverGeometry_stackNat (s : State) (fit : recoverStack ≤ (s.gpr .esp).toNat) :
    (recoverGeometry s).stack.toNat = (s.gpr .esp).toNat - 2128 := by
  rw [recoverGeometry_stack, sub_toNat (by unfold recoverStack at fit; omega)]

theorem recoverGeometry_wholeStack (s : State) (fit : recoverStack ≤ (s.gpr .esp).toNat) :
    (recoverGeometry s).wholeStack = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ := by
  unfold Geometry.wholeStack
  rw [recoverGeometry_stack, BitVec.sub_sub]
  change (⟨(s.gpr .esp - BitVec.ofNat 32 recoverStack).setWidth 64, recoverStack⟩ : Region) = _
  rw [Taint.sub_setWidth fit]

theorem recoverGeometry_arguments (s : State) (fit : recoverStack ≤ (s.gpr .esp).toNat)
    (high : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32) :
    (recoverGeometry s).argumentsRegion = ⟨argAddr s 0, 52⟩ := by
  unfold Geometry.argumentsRegion
  rw [recoverGeometry_stack]
  change (⟨(s.gpr .esp - BitVec.ofNat 32 2128).setWidth 64 + BitVec.ofNat 64 2132, 52⟩ : Region) = _
  rw [Taint.sub_setWidth (by unfold recoverStack at fit; omega : 2128 ≤ (s.gpr .esp).toNat)]
  have aa : argAddr s 0 = (s.gpr .esp).setWidth 64 + 4 :=
    byteAddr_add (by omega : (s.gpr .esp).toNat + 4 < 2 ^ 32)
  rw [aa, show BitVec.ofNat 64 2132 = BitVec.ofNat 64 2128 + 4 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
end VG.Proof.RsaPkcs1Sig.X86.Rcv
