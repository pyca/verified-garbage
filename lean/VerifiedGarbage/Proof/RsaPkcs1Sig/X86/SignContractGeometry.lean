module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignGeometry
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Weierstrass

/-! # Decode checked RSA's cdecl arguments into its public buffer geometry -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Bignum.X86

def signGeometry (s : State) : Geometry where
  stack := s.gpr .esp - 16 - BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes
  output := arg s 0
  workspace := arg s 19
  sources := fun i => arg s (if i.val < 2 then 2 + 2 * i.val else if i.val = 2 then 7 else 3 + 2 * i.val)
  length := (arg s 3).toNat
  hash := arg s 6
  digestLength := (arg s 8).toNat
  exponentLength := (arg s 5).toNat
  pLength := (arg s 10).toNat
  qLength := (arg s 12).toNat
  scratchLength := (arg s 20).toNat

def signBytes (s : State) (i : Fin 8) : List Byte :=
  Spec.Rsa.bytesAt s.mem (byteAddr ((signGeometry s).sources i)) ((signGeometry s).sourceLength i)

theorem signGeometry_stack (s : State) :
    (signGeometry s).stack = s.gpr .esp - BitVec.ofNat 32 1136 := by
  change s.gpr .esp - 16 - 1120 = _
  rw [BitVec.sub_sub]
  rfl

theorem signGeometry_stackNat (s : State) (fit : sigStack ≤ (s.gpr .esp).toNat) :
    (signGeometry s).stack.toNat = (s.gpr .esp).toNat - 1136 := by
  rw [signGeometry_stack, sub_toNat (by unfold sigStack at fit; omega)]

theorem signGeometry_wholeStack (s : State) (fit : sigStack ≤ (s.gpr .esp).toNat) :
    (signGeometry s).wholeStack = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ := by
  unfold Geometry.wholeStack
  rw [signGeometry_stack, BitVec.sub_sub]
  change (⟨(s.gpr .esp - BitVec.ofNat 32 sigStack).setWidth 64, sigStack⟩ : Region) = _
  rw [Taint.sub_setWidth fit]

theorem signGeometry_arguments (s : State) (fit : sigStack ≤ (s.gpr .esp).toNat)
    (high : (s.gpr .esp).toNat + 88 ≤ 2 ^ 32) :
    (signGeometry s).argumentsRegion = ⟨argAddr s 0, 84⟩ := by
  unfold Geometry.argumentsRegion
  rw [signGeometry_stack]
  change (⟨(s.gpr .esp - BitVec.ofNat 32 1136).setWidth 64 + BitVec.ofNat 64 1140, 84⟩ : Region) = _
  rw [Taint.sub_setWidth (by unfold sigStack at fit; omega : 1136 ≤ (s.gpr .esp).toNat)]
  have aa : argAddr s 0 = (s.gpr .esp).setWidth 64 + 4 :=
    byteAddr_add (by omega : (s.gpr .esp).toNat + 4 < 2 ^ 32)
  rw [aa, show BitVec.ofNat 64 1140 = BitVec.ofNat 64 1136 + 4 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
end VG.Proof.RsaPkcs1Sig.X86.Sgn
