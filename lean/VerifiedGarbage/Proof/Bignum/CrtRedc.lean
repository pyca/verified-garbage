import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Impl.Bignum.CrtLayout

/-!
# RSA with the CRT: `redc`'s ranges and chunks

`redc j`, in a prime's workspace (`X`, `w_X` words, `R = 2^(64 w_X)`),
reduces the number `x` of the modulus' array `j` (`w` words) in chunks of
`w_X` words, `x = Σ x_k R^k`, as `A := (A R⁻¹ + x_k R⁻¹) mod X` for each
chunk from the lowest. These are the facts about it that do not depend on
the target: what it changes (`redcRanges`), the words it has read after `k`
chunks (`lowW`) and its `K = ⌈w / w_X⌉` chunks (`lt_chunks`).
-/

namespace VG.Proof.Bignum

open VG VG.Impl.Bignum VG.Impl.Bignum.Crt

/-- What `redc` changes in the prime's workspace. -/
def redcRanges (wx : Nat) : List (Nat × Nat) :=
  [(slot wx Public.aAcc, 8 * (wx + 2)), (slot wx Public.aTmp, 8 * (wx + 2)), (slot wx aXc, 8 * (wx + 2)),
    (slot wx aChunk, 8 * (wx + 2)), (slot wx aT, 8 * (wx + 2)), (8 * sSrc, 8), (8 * sRem, 8)]

theorem redcRanges_ok (wx : Nat) : ∀ r ∈ redcRanges wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 := by
  have := hdr_lt_slot wx 0 (show 31 < 32 by decide)
  have := slot_le (w := wx) (show 0 < 8 by decide)
  have := slot_le (w := wx) (show Public.aAcc < 8 by decide)
  have := slot_le (w := wx) (show Public.aTmp < 8 by decide)
  have := slot_le (w := wx) (show aXc < 8 by decide)
  have := slot_le (w := wx) (show aChunk < 8 by decide)
  have := slot_le (w := wx) (show aT < 8 by decide)
  have h1 : slot wx 0 ≤ slot wx Public.aAcc := by unfold slot; omega
  have h2 : slot wx 0 ≤ slot wx Public.aTmp := by unfold slot; omega
  have h3 : slot wx 0 ≤ slot wx aXc := by unfold slot; omega
  have h4 : slot wx 0 ≤ slot wx aChunk := by unfold slot; omega
  have h5 : slot wx 0 ≤ slot wx aT := by unfold slot; omega
  simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [sSrc, sRem, sFn] at * <;> omega

theorem redcRanges_arr (wx : Nat) {j : Nat} (hj : j < 8) (h1 : j ≠ Public.aAcc) (h2 : j ≠ Public.aTmp)
    (h3 : j ≠ aXc) (h4 : j ≠ aChunk) (h5 : j ≠ aT) :
    ∀ r ∈ redcRanges wx, slot wx j + 8 * (wx + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot wx j := by
  have := hdr_lt_slot wx j (show 31 < 32 by decide)
  have s1 := slot_sep (w := wx) h1
  have s2 := slot_sep (w := wx) h2
  have s3 := slot_sep (w := wx) h3
  have s4 := slot_sep (w := wx) h4
  have s5 := slot_sep (w := wx) h5
  have := hj
  simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [sSrc, sRem, sFn] at * <;> omega

theorem wv_split (m : Mem) (p : Addr) (d : Nat) {n k L : Nat} (h : n + k = L) :
    wv m p d L = wv m p d n + 2 ^ (64 * n) * wv m p (d + 8 * n) k := by
  subst h; exact wv_add m p d n k

/-- The words of `x` read after `k` chunks. -/
def lowW (w wx k : Nat) : Nat := min w (k * wx)

/-- `k < K = ⌈w / w_X⌉` iff the first `k` chunks leave words. -/
theorem lt_chunks {w wx k : Nat} (hwx : 1 ≤ wx) : k < (w + wx - 1) / wx ↔ k * wx < w := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega), Nat.add_mul, Nat.one_mul]
  omega

theorem sMaskX_redc (wx : Nat) : ∀ r ∈ redcRanges wx, 8 * sMaskX + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMaskX := by
  intro r hr
  simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  have := hdr_lt_slot wx Public.aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot wx Public.aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot wx aXc (show 31 < 32 by decide)
  have := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
  have := hdr_lt_slot wx aT (show 31 < 32 by decide)
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sMaskX, sSrc, sRem, sFn] <;> omega

/-- `K = ⌈w / w_X⌉`. -/
abbrev nChunks (w wx : Nat) : Nat := (w + wx - 1) / wx

end VG.Proof.Bignum
