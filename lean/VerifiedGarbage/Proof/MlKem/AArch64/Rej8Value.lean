module

public import VerifiedGarbage.Impl.MlKem.AArch64.Rej8
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit

/-! # Exact acceptance bits and compaction masks for eight ML-KEM candidates -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Impl.MlKem.AArch64.Rej8

/-- The halfword subtraction cannot confuse a rejected 12-bit candidate
with a negative value. -/
theorem candidate_bit (z : BitVec 16) (hz : z.toNat < 4096) :
    (z - 3329) >>> 15 = if z.toNat < 3329 then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub]
  have hq : (3329 : BitVec 16).toNat = 3329 := rfl
  have h1 : (1 : BitVec 16).toNat = 1 := rfl
  have h0 : (0 : BitVec 16).toNat = 0 := rfl
  by_cases h : z.toNat < 3329
  · rw [ite_eq_left h]
    simp only [hq, h1, Nat.shiftRight_eq_div_pow, Nat.reducePow] at hz ⊢
    omega
  · rw [ite_eq_right h]
    simp only [hq, h0, Nat.shiftRight_eq_div_pow, Nat.reducePow] at hz ⊢
    omega

/-- Accepted indices are always valid source halfwords. -/
theorem accepted_mem {mask i : Nat} (h : i ∈ acceptedLanes mask) : i < 8 := by
  exact List.mem_range.mp (List.mem_filter.mp h).1

/-- At most eight candidates are accepted in a vector step. -/
theorem accepted_length (mask : Nat) : (acceptedLanes mask).length ≤ 8 := by
  simpa only [acceptedLanes, List.length_range] using List.length_filter_le (fun i => (mask / 2^i)%2 == 1) (List.range 8)

/-- The table packs precisely the accepted halfwords, in their source order. -/
theorem row_length (mask : Nat) : (tableRow mask).length = 2 * (acceptedLanes mask).length := by
  simp only [tableRow, List.length_flatMap]
  induction acceptedLanes mask with
  | nil => simp
  | cons a as ih => simp_all [Nat.mul_add, Nat.add_comm]

/-- The horizontal halfword sum encodes both the mask and its population.
The low byte is the table index; the high byte is the output advance. -/
def packedCount (mask : Nat) : Nat :=
  ((acceptedLanes mask).map fun i => 256 + 2^i).sum

theorem packedCount_exact {mask : Nat} (hm : mask < 256) :
    packedCount mask = mask + 256 * (acceptedLanes mask).length := by
  have finite : ∀ mask < 256,
      packedCount mask = mask + 256 * (acceptedLanes mask).length := by decide +kernel
  exact finite mask hm

theorem packedCount_mask {mask : Nat} (hm : mask < 256) :
    packedCount mask % 256 = mask := by
  rw [packedCount_exact hm]
  omega

theorem packedCount_count {mask : Nat} (hm : mask < 256) :
    packedCount mask / 256 = (acceptedLanes mask).length := by
  rw [packedCount_exact hm]
  omega

theorem packedCount_bound {mask : Nat} (hm : mask < 256) : packedCount mask < 2304 := by
  rw [packedCount_exact hm]
  have := accepted_length mask
  omega

end VG.Proof.MlKem.AArch64.Rej8
