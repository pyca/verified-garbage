module

public import VerifiedGarbage.Proof.Bignum.CrtGPow
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA with the CRT: what `p`'s phase changes

`p`'s phase changes, in the modulus' workspace, `gPow`'s ranges and `X`
(`pRanges`), and the prime's workspace (`xRange`); these are the words and
numbers it keeps.
-/

@[expose] public section

namespace VG.Proof.Bignum

open VG VG.Impl.Bignum

/-- What `p`'s phase changes in the modulus' workspace. -/
def pRanges (w : Nat) : List (Nat × Nat) := gRanges w ++ [(slot w Public.aX, 8 * (w + 2))]

theorem pRanges_le (w : Nat) : ∀ r ∈ pRanges w, r.1 + r.2 ≤ slot w 8 := by
  have := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  have := slot_le (w := w) (show Public.aAcc < 8 by decide)
  have := slot_le (w := w) (show Public.aTmp < 8 by decide)
  have := slot_le (w := w) (show Public.aY < 8 by decide)
  have := slot_le (w := w) (show Public.aX < 8 by decide)
  intro r hr
  simp only [pRanges, gRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega

theorem pxR_bound {w o wx : Nat} (hlo : slot w 8 ≤ o) :
    ∀ r ∈ pRanges w ++ [xRange o wx], 8 * 22 ≤ r.1 ∧ r.1 + r.2 ≤ o + slot wx 8 + wsTab wx := by
  have := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aY (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aX (show 31 < 32 by decide)
  have := slot_le (w := w) (show Public.aAcc < 8 by decide)
  have := slot_le (w := w) (show Public.aTmp < 8 by decide)
  have := slot_le (w := w) (show Public.aY < 8 by decide)
  have := slot_le (w := w) (show Public.aX < 8 by decide)
  have : 8 * 17 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  intro r hr
  simp only [pRanges, gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega

theorem Frm.px_hdr {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (pRanges w ++ [xRange o wx]) m m')
    (hlo : slot w 8 ≤ o) {i : Nat} (hi : i < 32) (h1 : i ≠ Crt.sD) (h2 : i ≠ Public.sCnt) :
    word m' B (8 * i) = word m B (8 * i) := hf.word_eq (fun r hr => by
  have hb := pxR_bound hlo r hr
  have := hdr_lt_slot w Public.aAcc (show i < 32 from hi)
  have := hdr_lt_slot w Public.aTmp (show i < 32 from hi)
  have := hdr_lt_slot w Public.aY (show i < 32 from hi)
  have := hdr_lt_slot w Public.aX (show i < 32 from hi)
  have := slot_le (w := w) (show Public.aX < 8 by decide)
  simp only [pRanges, gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · show 8 * i + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * i
    unfold Crt.sD sFn at h1 ⊢; omega
  · show 8 * i + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * i
    unfold Public.sCnt sFn at h2 ⊢; omega
  · exact Or.inl (by omega)
  · exact Or.inl (by simp only at hb ⊢; omega)) (by omega)

theorem Frm.px_above {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (pRanges w ++ [xRange o wx]) m m')
    (hlo : slot w 8 ≤ o) {d : Nat} (hd : o + slot wx 8 + wsTab wx ≤ d) (hd' : d + 8 ≤ 2 ^ 64) :
    word m' B d = word m B d :=
  hf.word_eq (fun r hr => Or.inr (by have := pxR_bound hlo r hr; omega)) hd'

theorem Frm.px_wv {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (pRanges w ++ [xRange o wx]) m m')
    (hlo : slot w 8 ≤ o) (hz : B.toNat + slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ Public.aAcc)
    (h2 : j ≠ Public.aTmp) (h3 : j ≠ Public.aY) (h4 : j ≠ Public.aX) : wv m' B (slot w j) w = wv m B (slot w j) w := by
  have hj8 := slot_le (w := w) hj
  have arr : ∀ {k}, j ≠ k → slot w j + 8 * w ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j := fun hk =>
    (slot_sep (w := w) hk).imp_left fun h => by omega_using [h]
  refine hf.wv_eq (fun r hr => ?_) (by omega_using [hj8, hz])
  simp only [pRanges, gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact arr h1
  · exact arr h2
  · exact arr h3
  · exact Or.inr (hdr_lt_slot w j (show Crt.sD < 32 by decide))
  · exact Or.inr (hdr_lt_slot w j (show Public.sCnt < 32 by decide))
  · exact arr h4
  · exact Or.inl (by dsimp only; omega_using [hj8, hlo])

/-- The first word of an array that `p`'s phase does not write. -/
theorem Frm.px_word {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (pRanges w ++ [xRange o wx]) m m')
    (hlo : slot w 8 ≤ o) (hz : B.toNat + slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ Public.aAcc)
    (h2 : j ≠ Public.aTmp) (h3 : j ≠ Public.aY) (h4 : j ≠ Public.aX) : word m' B (slot w j) = word m B (slot w j) := by
  have hj8 := slot_le (w := w) hj
  have arr : ∀ {k}, j ≠ k → slot w j + 8 ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j := fun hk =>
    (slot_sep (w := w) hk).imp_left fun h => by omega_using [h]
  refine hf.word_eq (fun r hr => ?_) (by omega_using [hj8, hz])
  simp only [pRanges, gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact arr h1
  · exact arr h2
  · exact arr h3
  · exact Or.inr (hdr_lt_slot w j (show Crt.sD < 32 by decide))
  · exact Or.inr (hdr_lt_slot w j (show Public.sCnt < 32 by decide))
  · exact arr h4
  · exact Or.inl (by dsimp only; omega_using [hj8, hlo])

end VG.Proof.Bignum
