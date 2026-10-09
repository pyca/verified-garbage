import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMath
import VerifiedGarbage.Proof.Framework.AArch64.Simd

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour

/-- The loaded 16-byte compaction mask. -/
def shuffleWord (mask : Nat) : BitVec 128 := BitVec.ofNat 128 (bytesWord (shuffleBytes mask))

theorem indices_length (mask : Nat) : (acceptedIndices mask).length≤4 := by
  have := List.length_filter_le (fun i => mask / 2^i % 2 == 1) (List.range 4)
  simpa only [acceptedIndices,List.length_range] using this

theorem index_bound : ∀mask<16,∀i<(acceptedIndices mask).length,(acceptedIndices mask)[i]!<4 := by decide

theorem shuffle_byte : ∀mask<16,∀i<(acceptedIndices mask).length,∀j<4,
    vbyte (shuffleWord mask) (4*i+j) = BitVec.ofNat 8 (4*(acceptedIndices mask)[i]!+j) := by decide

/-- Each mask records exactly four independent acceptance decisions. -/
def maskOf (a b c d : Bool) : Nat := a.toNat+2*b.toNat+4*c.toNat+8*d.toNat

theorem maskOf_lt (a b c d : Bool) : maskOf a b c d<16 := by cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem maskOf_indices : ∀a b c d : Bool,
    acceptedIndices (maskOf a b c d) =
      (if a then [0] else []) ++ (if b then [1] else []) ++
      (if c then [2] else []) ++ (if d then [3] else []) := by decide

/-- The count stored beside the mask is precisely the number accepted. -/
theorem maskOf_count : ∀a b c d : Bool,
    (acceptedIndices (maskOf a b c d)).length=a.toNat+b.toNat+c.toNat+d.toNat := by decide

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
