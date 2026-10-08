import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Impl.Bignum.CrtLayout

/-!
# RSA with the CRT: `G = 2^E mod n`

`gPow` computes, in the modulus' workspace (`w` words), `G = 2^E mod n` for
`E = 64 w_X (K + 1)` and `K = ⌈w / w_X⌉` (`kBounds`): `D = E - 64 w`
(`gD`, `gD_bounds`), then a squaring and a doubling under each bit of `D`
from the top (`and_pow_beq`, `div_bit`). These are its facts that do not
depend on the target.
-/

namespace VG.Proof.Bignum

open VG VG.Impl.Bignum VG.Impl.Bignum.Public

/-- `K = ⌈w / w_X⌉`: `w ≤ K w_X < w + w_X`. -/
theorem kBounds {w wx : Nat} (hwx : 1 ≤ wx) :
    w ≤ (w + wx - 1) / wx * wx ∧ (w + wx - 1) / wx * wx < w + wx := by
  have h1 := Nat.div_add_mod (w + wx - 1) wx
  have h2 := Nat.mod_lt (w + wx - 1) (show 0 < wx by omega)
  rw [Nat.mul_comm] at h1
  omega

/-- `D / 64 = (K + 1) w_X - w`. -/
def gC (w wx : Nat) : Nat := (w + wx - 1) / wx * wx + wx - w

/-- `D = 64 ((K + 1) w_X - w)`. -/
def gD (w wx : Nat) : Nat := 64 * gC w wx

/-- The top word of `m`'s `w` words is `m / 2^(64 (w - 1))`. -/
theorem wv_top (m : Mem) (B : Addr) (o w : Nat) (hw : 1 ≤ w) :
    (word m B (o + 8 * (w - 1))).toNat = wv m B o w / 2 ^ (64 * (w - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  rw [Nat.add_sub_cancel, wv, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (wv_lt m B o k), Nat.zero_add]

/-- A nonzero top word bounds the number below. -/
theorem le_of_top {N k : Nat} (h : N / 2 ^ k ≠ 0) : 2 ^ k ≤ N :=
  Nat.le_of_not_lt fun h' => h (Nat.div_eq_of_lt h')

/-- `2^D` is below `m` when `D / 64 < w - 1` and `m`'s top word is not 0:
`gPow`'s fast path. -/
theorem gFast_lt {N w c : Nat} (hc : c < w - 1) (h : N / 2 ^ (64 * (w - 1)) ≠ 0) : 2 ^ (64 * c) < N :=
  Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) (by omega)) (le_of_top h)

theorem and_pow_beq (D k : Nat) (hk : k < 64) :
    (BitVec.ofNat 64 D &&& BitVec.ofNat 64 (2 ^ k) == 0) = decide (D / 2 ^ k % 2 = 0) := by
  have e : BitVec.ofNat 64 (2 ^ k) = BitVec.twoPow 64 k := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, BitVec.toNat_twoPow]
  rw [e, BitVec.and_twoPow, BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : D / 2 ^ k % 2 = 0
  · simp [h]
  · have h1 : D / 2 ^ k % 2 = 1 := by omega
    have h2 : BitVec.twoPow 64 k ≠ 0#64 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_twoPow_of_lt hk] at this
      exact absurd this (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k))
    simp [h1, hk, h2]

theorem div_bit (D k : Nat) : 2 * (D / 2 ^ (k + 1)) + D / 2 ^ k % 2 = D / 2 ^ k := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega

/-- What `gPow` changes. -/
def gRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (8 * Crt.sD, 8),
    (8 * sCnt, 8)]

theorem gD_bounds {w wx : Nat} (hwx : 1 ≤ wx) (hwx' : wx ≤ w) (hw30 : w < 2 ^ 30) :
    0 < gD w wx ∧ gD w wx < 2 ^ 62 ∧
      gD w wx + 64 * w = 64 * wx * ((w + wx - 1) / wx + 1) := by
  obtain ⟨hK1, hK2⟩ := kBounds (w := w) hwx
  unfold gD gC
  rw [Nat.mul_succ, Nat.mul_assoc 64 wx, Nat.mul_comm wx]
  omega

/-- The modulus' arrays but `Y`, the accumulator and the temporary are kept
by a change within `gRanges` and a prime's workspace. -/
theorem Frm.gx_wv {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (gRanges w ++ [xRange o wx]) m m')
    (hlo : slot w 8 ≤ o) (hz : B.toNat + slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ Public.aAcc)
    (h2 : j ≠ Public.aTmp) (h3 : j ≠ Public.aY) : wv m' B (slot w j) w = wv m B (slot w j) w := by
  have := slot_le (w := w) hj
  have := hdr_lt_slot w j (show 31 < 32 by decide)
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  have s3 := slot_sep (w := w) h3
  refine hf.wv_eq (fun r hr => ?_) (by omega)
  simp only [gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega

theorem gRanges_le (w : Nat) : ∀ r ∈ gRanges w, r.1 + r.2 ≤ slot w 8 := by
  have := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have := slot_le (w := w) (show Public.aAcc < 8 by decide)
  have := slot_le (w := w) (show Public.aTmp < 8 by decide)
  have := slot_le (w := w) (show Public.aY < 8 by decide)
  simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega

theorem gxRanges_le {w o wx : Nat} (hlo : slot w 8 ≤ o) :
    ∀ r ∈ gRanges w ++ [xRange o wx], r.1 + r.2 ≤ o + slot wx 8 + tabBytes wx := by
  have hX8 : 8 * 17 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · have := gRanges_le w r hr; omega
  · rw [List.mem_singleton.mp hr]; simp only [xRange]; omega

/-- The modulus' header words but `sD`'s and `sCnt`'s, past a change within
`gRanges` and a prime's workspace. -/
theorem Frm.gx_hdr {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (gRanges w ++ [xRange o wx]) m m')
    (hlo : slot w 8 ≤ o) {i : Nat} (hi : i < 32) (h1 : i ≠ Crt.sD)
    (h2 : i ≠ Public.sCnt) : word m' B (8 * i) = word m B (8 * i) := by
  have := hdr_lt_slot w Public.aAcc hi
  have := hdr_lt_slot w Public.aTmp hi
  have := hdr_lt_slot w Public.aY hi
  have := hdr_lt_slot w 8 hi
  refine hf.word_eq (fun r hr => ?_) (by omega)
  simp only [gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · show 8 * i + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * i
    unfold Crt.sD sFn at h1 ⊢; omega
  · show 8 * i + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * i
    unfold Public.sCnt sFn at h2 ⊢; omega
  · exact Or.inl (by omega)

/-- A prime's workspace header past a change within `gRanges`. -/
theorem WsAt.of_g {m m' : Mem} {B : Addr} {w o wx : Nat} {mx : BitVec 64} (h : WsAt m B o wx mx)
    (hf : Frm B (gRanges w) m m') (hlo : slot w 8 ≤ o) (hoL : B.toNat + o + slot wx 8 ≤ 2 ^ 64) :
    WsAt m' B o wx mx :=
  h.of_words fun i hi => by
    have : 8 * 32 ≤ slot wx 8 := by unfold slot hdrBytes; omega
    rw [word_off, word_off]
    exact hf.word_eq (fun r hr => Or.inr (by have := gRanges_le w r hr; omega)) (by omega)

end VG.Proof.Bignum
