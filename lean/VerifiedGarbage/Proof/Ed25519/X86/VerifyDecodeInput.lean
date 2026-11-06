module

public import VerifiedGarbage.Proof.Ed25519.X86.PointDecode
public import VerifiedGarbage.Proof.Ed25519.X86.InputSlice
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.Decode
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem decodeNumber_spec (bs : List Byte) (hl : bs.length = 32) :
    decodeNumber (Spec.Ed25519.decodeLE bs) = Spec.Ed25519.decodePoint bs := by
  rw [decodePoint32 bs hl]
  by_cases hy : Spec.Ed25519.decodeLE bs % 2 ^ 255 < Spec.X25519.P
  · rw [decodeNumber, dite_eq_left hy, ite_eq_left hy, toFe_of_lt _ hy]
    rfl
  · rw [decodeNumber, dite_eq_right hy, ite_eq_right hy]

def inputPoint (s : State) (i : Nat) : Option Spec.Ed25519.Point :=
  Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem ((arg s i + BitVec.ofNat 32 0).setWidth 64) 32)

theorem inputPoint_number {s : State} {i : Nat} (hi : SlicePre s 3 (arg s i + BitVec.ofNat 32 0) 32) :
    decodeNumber (fe s.mem (arg s i + BitVec.ofNat 32 0) 0) = inputPoint s i := by
  have hv : fe s.mem (arg s i + BitVec.ofNat 32 0) 0 = Spec.Ed25519.decodeLE
      (Spec.Ed25519.bytesAt s.mem ((arg s i + BitVec.ofNat 32 0).setWidth 64) 32) := by
    rw [← addr_zero (arg s i + BitVec.ofNat 32 0)]
    exact (decode_words s.mem 8 (by have := hi.fit; omega_using [this])).symm
  exact (congrArg decodeNumber hv).trans (decodeNumber_spec _
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]))

end VG.Proof.Ed25519.X86
