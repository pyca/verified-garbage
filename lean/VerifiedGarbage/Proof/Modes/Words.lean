import VerifiedGarbage.Proof.Modes.Unchain
import VerifiedGarbage.Proof.Modes.Ctr

/-!
# Words stored one at a time, in memory

`over m P n f`: the memory `m` with the `n` bytes at `P` given by `f`. A
mode's word loops (a copy, a XOR into a block) store a block a word at a
time; `over_step` adds the next word's 8 bytes, so a loop's memory is
`over` of its first `8 w` bytes after `w` words, on any 64-bit target.
-/

namespace VG.Proof.Modes

open VG

/-- The memory `m` with the `n` bytes at `P` given by `f`. -/
def over (m : Mem) (P : Addr) (n : Nat) (f : Nat → Byte) : Mem :=
  fun x => if (x - P).toNat < n then f (x - P).toNat else m x

theorem over_zero (m : Mem) (P : Addr) (f : Nat → Byte) : over m P 0 f = m := by
  funext x; simp [over]

theorem over_at {m : Mem} {P : Addr} {n : Nat} {f : Nat → Byte} {i : Nat} (hi : i < n) (hn : n ≤ 2 ^ 64) :
    over m P n f (P + BitVec.ofNat 64 i) = f i := by
  simp only [over]; rw [off_self P (by omega), ite_eq_left hi]

theorem over_out {m : Mem} {P : Addr} {n : Nat} {f : Nat → Byte} {x : Addr} (hx : ¬ (x - P).toNat < n) :
    over m P n f x = m x := by
  simp only [over]; rw [ite_eq_right hx]

/-- The byte at `x` is word `d / 8` of `P`'s exactly when its offset from
`P` is in `[d, d + 8)`. -/
theorem sub_add_lt (x P : Addr) {d : Nat} (hd : d + 8 ≤ 2 ^ 64) :
    (x - (P + BitVec.ofNat 64 d)).toNat < 8 ↔ d ≤ (x - P).toNat ∧ (x - P).toNat < d + 8 := by
  bv_omega

theorem sub_add_eq (x P : Addr) {d : Nat} (hd : d + 8 ≤ 2 ^ 64) (h : d ≤ (x - P).toNat) :
    (x - (P + BitVec.ofNat 64 d)).toNat = (x - P).toNat - d := by
  bv_omega

/-- The next word: a memory that is `over m P (8 w) f` but in word `w`,
which holds `f`'s next 8 bytes, is `over m P (8 w + 8) f`. -/
theorem over_step {m m' : Mem} {P : Addr} {w : Nat} {f : Nat → Byte} (hw : 8 * w + 8 ≤ 2 ^ 64)
    (h : ∀ x, m' x = if (x - (P + BitVec.ofNat 64 (8 * w))).toNat < 8 then
      f (8 * w + (x - (P + BitVec.ofNat 64 (8 * w))).toNat) else over m P (8 * w) f x) :
    m' = over m P (8 * w + 8) f := by
  funext x
  rw [h x]
  by_cases hx : (x - (P + BitVec.ofNat 64 (8 * w))).toNat < 8
  · have := (sub_add_lt x P hw).mp hx
    rw [ite_eq_left hx, sub_add_eq x P hw this.1, show 8 * w + ((x - P).toNat - 8 * w) = (x - P).toNat by omega]
    simp only [over]; rw [ite_eq_left (by omega)]
  · rw [ite_eq_right hx]
    have := mt (sub_add_lt x P hw).mpr hx
    simp only [over]
    by_cases h1 : (x - P).toNat < 8 * w
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1, ite_eq_right (by omega)]

/-- A byte at an offset from the same base as `over`'s block. -/
theorem over_off (m : Mem) (X : Addr) {d n t : Nat} (f : Nat → Byte) (ht : t < 2 ^ 64) (hd : d + n ≤ 2 ^ 64)
    (hn : 0 < n) :
    over m (X + BitVec.ofNat 64 d) n f (X + BitVec.ofNat 64 t) =
      if d ≤ t ∧ t < d + n then f (t - d) else m (X + BitVec.ofNat 64 t) := by
  split
  · rename_i h
    rw [show X + BitVec.ofNat 64 t = X + BitVec.ofNat 64 d + BitVec.ofNat 64 (t - d) by
      rw [VG.Offset.add_add, Nat.add_sub_cancel' h.1], over_at (by omega) (by omega)]
  · exact over_out (off_sub_not X (by omega) ht hn hd)

/-- Bytes of a block other than `P`'s stay through `over`. -/
theorem over_sep {m : Mem} {P Q : Addr} {n k : Nat} {f : Nat → Byte} (hd : Region.Disjoint ⟨P, n⟩ ⟨Q, k⟩)
    {i : Nat} (hi : i < k) (hk : k ≤ 2 ^ 64) : over m P n f (Q + BitVec.ofNat 64 i) = m (Q + BitVec.ofNat 64 i) :=
  over_out (not_near (fun y h1 h2 => hd y h2 h1) hi (Nat.le_refl _) hk)

/-- `over` changes only its block. -/
theorem over_frame (m : Mem) (P : Addr) (n : Nat) (f : Nat → Byte) : Frame [⟨P, n⟩] m (over m P n f) :=
  fun _ hx => over_out fun h => hx _ List.mem_cons_self (by simp only [Region.Contains]; omega)

/-- Byte `r` of block `q` of the blocks of `L` bytes at `D`, through `over`
of block `p`. -/
theorem over_blk (m : Mem) (D : Addr) {L n p q r : Nat} (f : Nat → Byte) (hp : p < n) (hq : q < n) (hr : r < L)
    (hn : L * n ≤ 2 ^ 64) :
    over m (D + BitVec.ofNat 64 (L * p)) L f (D + BitVec.ofNat 64 (L * q + r)) =
      if q = p then f r else m (D + BitVec.ofNat 64 (L * q + r)) := by
  have := idx_lt (L := L) hq
  have := idx_lt (L := L) hp
  split
  · rename_i h; subst h; rw [← VG.Offset.add_add, over_at hr (by omega)]
  · rename_i h
    refine over_out (off_sub_not D ?_ (by omega) (by omega) (by omega))
    rcases Nat.lt_or_gt_of_ne h with h | h
    · have := idx_lt (L := L) h; omega
    · have := idx_lt (L := L) h; omega

end VG.Proof.Modes
