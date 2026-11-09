module

public import VerifiedGarbage.Impl.MlKem.AArch64.Rej8
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

/-! # Exact acceptance bits and compaction masks for eight ML-KEM candidates -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Impl.MlKem.AArch64.Rej8

/-- Accepted indices are always valid source halfwords. -/
theorem accepted_mem {mask i : Nat} (h : i ∈ acceptedLanes mask) : i < 8 := by
  exact List.mem_range.mp (List.mem_filter.mp h).1

/-- At most eight candidates are accepted in a vector step. -/
theorem accepted_length (mask : Nat) : (acceptedLanes mask).length ≤ 8 := by
  simpa only [acceptedLanes, List.length_range] using List.length_filter_le (fun i => (mask / 2^i)%2 == 1) (List.range 8)

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
