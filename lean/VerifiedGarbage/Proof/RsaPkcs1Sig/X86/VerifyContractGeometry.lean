module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyGeometry
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Weierstrass

/-! # Decode checked RSA's cdecl arguments into its public buffer geometry -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86

def verifyGeometry (s : State) : Geometry where
  stack := s.gpr .esp - 16 - BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes
  workspace := arg s 9
  sources := fun i => arg s (match i.val with | 0 => 0 | 1 => 2 | 2 => 5 | 3 => 7 | _ => 11)
  length := (arg s 1).toNat
  hash := arg s 4
  exponentLength := (arg s 3).toNat
  digestLength := (arg s 6).toNat
  signatureLength := (arg s 8).toNat
  preLength := (arg s 12).toNat
  scratchLength := (arg s 10).toNat

def verifyBytes (s : State) (i : Fin 5) : List Byte :=
  Spec.Rsa.bytesAt s.mem (byteAddr ((verifyGeometry s).sources i)) ((verifyGeometry s).sourceLength i)

theorem verifyGeometry_stack (s : State) :
    (verifyGeometry s).stack = s.gpr .esp - BitVec.ofNat 32 2128 := by
  change s.gpr .esp - 16 - 2112 = _
  rw [BitVec.sub_sub]
  rfl

theorem verifyGeometry_stackNat (s : State) (fit : verifyStack ≤ (s.gpr .esp).toNat) :
    (verifyGeometry s).stack.toNat = (s.gpr .esp).toNat - 2128 := by
  rw [verifyGeometry_stack, sub_toNat (by unfold verifyStack at fit; omega)]

theorem verifyGeometry_wholeStack (s : State) (fit : verifyStack ≤ (s.gpr .esp).toNat) :
    (verifyGeometry s).wholeStack = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ := by
  unfold Geometry.wholeStack
  rw [verifyGeometry_stack, BitVec.sub_sub]
  change (⟨(s.gpr .esp - BitVec.ofNat 32 verifyStack).setWidth 64, verifyStack⟩ : Region) = _
  rw [Taint.sub_setWidth fit]

theorem verifyGeometry_arguments (s : State) (fit : verifyStack ≤ (s.gpr .esp).toNat)
    (high : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32) :
    (verifyGeometry s).argumentsRegion = ⟨argAddr s 0, 52⟩ := by
  unfold Geometry.argumentsRegion
  rw [verifyGeometry_stack]
  change (⟨(s.gpr .esp - BitVec.ofNat 32 2128).setWidth 64 + BitVec.ofNat 64 2132, 52⟩ : Region) = _
  rw [Taint.sub_setWidth (by unfold verifyStack at fit; omega : 2128 ≤ (s.gpr .esp).toNat)]
  have aa : argAddr s 0 = (s.gpr .esp).setWidth 64 + 4 :=
    byteAddr_add (by omega : (s.gpr .esp).toNat + 4 < 2 ^ 32)
  rw [aa, show BitVec.ofNat 64 2132 = BitVec.ofNat 64 2128 + 4 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
end VG.Proof.RsaPkcs1Sig.X86.Ver
