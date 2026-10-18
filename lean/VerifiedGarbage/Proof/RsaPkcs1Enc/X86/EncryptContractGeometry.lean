module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptEntryReady
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI

/-! # Decode checked RSA's cdecl arguments into its public buffer geometry -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Proof.Bignum.X86

def encryptGeometry (s : State) : Geometry where
  stack := s.gpr .esp - 16 - BitVec.ofNat 32 VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes
  output := arg s 0
  workspace := arg s 10
  sources := fun i => arg s (if i.val < 4 then 2 + 2 * i.val else 12)
  length := (arg s 3).toNat
  exponentLength := (arg s 5).toNat
  messageLength := (arg s 7).toNat
  paddingLength := (arg s 9).toNat
  preLength := (arg s 13).toNat
  scratchLength := (arg s 11).toNat

def encryptBytes (s : State) (i : Fin 5) : List Byte :=
  Spec.Rsa.bytesAt s.mem (byteAddr ((encryptGeometry s).sources i)) ((encryptGeometry s).sourceLength i)

theorem encryptGeometry_stack (s : State) :
    (encryptGeometry s).stack = s.gpr .esp - BitVec.ofNat 32 1104 := by
  change s.gpr .esp - 16 - 1088 = _
  rw [BitVec.sub_sub]
  rfl

theorem encryptGeometry_stackNat (s : State) (fit : encryptStack ≤ (s.gpr .esp).toNat) :
    (encryptGeometry s).stack.toNat = (s.gpr .esp).toNat - 1104 := by
  rw [encryptGeometry_stack, sub_toNat (by unfold encryptStack at fit; omega)]

theorem encryptGeometry_wholeStack (s : State) (fit : encryptStack ≤ (s.gpr .esp).toNat) :
    (encryptGeometry s).wholeStack = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 encryptStack, encryptStack⟩ := by
  unfold Geometry.wholeStack
  rw [encryptGeometry_stack, BitVec.sub_sub]
  change (⟨(s.gpr .esp - BitVec.ofNat 32 encryptStack).setWidth 64, encryptStack⟩ : Region) = _
  rw [Taint.sub_setWidth fit]

theorem encryptGeometry_arguments (s : State) (fit : encryptStack ≤ (s.gpr .esp).toNat)
    (high : (s.gpr .esp).toNat + 60 ≤ 2 ^ 32) :
    (encryptGeometry s).argumentsRegion = ⟨argAddr s 0, 56⟩ := by
  unfold Geometry.argumentsRegion
  rw [encryptGeometry_stack]
  change (⟨(s.gpr .esp - BitVec.ofNat 32 1104).setWidth 64 + BitVec.ofNat 64 1108, 56⟩ : Region) = _
  rw [Taint.sub_setWidth (by unfold encryptStack at fit; omega : 1104 ≤ (s.gpr .esp).toNat)]
  have aa : argAddr s 0 = (s.gpr .esp).setWidth 64 + 4 :=
    byteAddr_add (by omega : (s.gpr .esp).toNat + 4 < 2 ^ 32)
  rw [aa, show BitVec.ofNat 64 1108 = BitVec.ofNat 64 1104 + 4 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
end VG.Proof.RsaPkcs1Enc.X86.Enc
