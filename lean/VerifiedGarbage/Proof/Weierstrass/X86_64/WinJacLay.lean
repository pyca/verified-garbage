import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJac
import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Weierstrass.Unch

/-!
# The Jacobian window method: where it keeps its numbers

The slots of `JacWinCfg.window` (`Impl/Weierstrass/X86_64/WinJac.lean`): the
ones it reads only (`jwRo`: the curve's `a` and `3b`, which the renamed
formulas name but do not read, zero and `P`), the others it writes
(`jwOther`: `R`, `D`, `-y` and the temporaries), and a grid of `85` slots
from `tbl` (`jg`): the table's 16 entries of five coordinates, entry `m`'s
coordinate `c` slot `5 (m - 1) + c`, then the selected entry `T`, slots
`80 … 84`. `JacWinLay` is what the proof needs of them, as `WinLay` for the
window method of `Window.lean`, for four-word numbers.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Proof.Mont VG.Proof.Weierstrass

/-- Slot `i` of the grid from the table. -/
def jg (K : JacWinCfg) (i : Nat) : Nat := K.tbl + 8 * K.M.n * i

/-- The grid: the table, then `T`. -/
def jwGrid (K : JacWinCfg) : List Nat := (List.range 85).map (jg K)

/-- The slots written but the grid's. -/
def jwOther (K : JacWinCfg) : List Nat :=
  [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z, K.neg, K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5]

/-- The slots read only. -/
def jwRo (K : JacWinCfg) : List Nat := [K.S.a, K.S.b3, K.zero, K.P.x, K.P.y, K.P.z]

def jwSlots (K : JacWinCfg) : List Nat := jwRo K ++ jwOther K ++ jwGrid K

def jwWs (K : JacWinCfg) : List Nat := jwOther K ++ jwGrid K

/-- What the method writes: its slots and the modulus's temporary area. -/
def jwW (K : JacWinCfg) : List (Nat × Nat) := (jwWs K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]

/-- What the loop writes: the other slots, `T`'s and the temporary area. -/
def jwLoopW (K : JacWinCfg) : List (Nat × Nat) :=
  (jwOther K ++ (List.range 5).map (fun c => jg K (80 + c))).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]

/-- The method's slots are in the working space and apart, those read only
not written, the others written distinct, the grid apart from them all, `T`
past the table, the counter's bits below `4096`, and the table of bits
(`5 J` bytes) apart from what is written. -/
structure JacWinLay (K : JacWinCfg) (size : Nat) : Prop where
  n4 : K.M.n = 4
  lay : Lay K.M size (· ∈ jwSlots K)
  ro : ∀ x ∈ jwRo K, x ∉ jwOther K
  nodup : (jwOther K).Nodup
  tbl : ∀ x ∈ jwRo K ++ jwOther K, x + 8 * K.M.n ≤ K.tbl ∨ K.tbl + 85 * (8 * K.M.n) ≤ x
  T : K.T = K.tbl + 16 * K.st
  J : 1 ≤ K.J ∧ K.J < 4096
  tbl31 : K.tbl < 2 ^ 31
  bits : K.bits + 5 * K.J ≤ size
  bits_w : ∀ w ∈ jwW K, K.bits + 5 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits

/-- `x ∈ l` for the method's lists. -/
macro "jw_mem" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_append,
  List.mem_singleton, true_or, or_true, jwSlots, jwWs, jwRo, jwOther, rcbW, rcbR,
  List.cons_append, List.nil_append]))

variable {K : JacWinCfg} {size : Nat}

theorem jg_mem_grid {i : Nat} (hi : i < 85) : jg K i ∈ jwGrid K :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem jg_mem {i : Nat} (hi : i < 85) : jg K i ∈ jwSlots K :=
  List.mem_append_right _ (jg_mem_grid hi)

theorem jg_ws {i : Nat} (hi : i < 85) : jg K i ∈ jwWs K :=
  List.mem_append_right _ (jg_mem_grid hi)

theorem other_mem {x : Nat} (h : x ∈ jwOther K) : x ∈ jwSlots K :=
  List.mem_append_left _ (List.mem_append_right _ h)

theorem other_ws {x : Nat} (h : x ∈ jwOther K) : x ∈ jwWs K := List.mem_append_left _ h

theorem ro_mem {x : Nat} (h : x ∈ jwRo K) : x ∈ jwSlots K :=
  List.mem_append_left _ (List.mem_append_left _ h)

theorem ws_mem {x : Nat} (h : x ∈ jwWs K) : x ∈ jwSlots K := by
  rcases List.mem_append.mp h with h | h
  · exact other_mem h
  · exact List.mem_append_right _ h

/-- Grid slots `i ≠ j` are apart. -/
theorem jg_apart (K : JacWinCfg) {i j : Nat} (h : i ≠ j) :
    jg K i + 8 * K.M.n ≤ jg K j ∨ jg K j + 8 * K.M.n ≤ jg K i := by
  unfold jg
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left; have := Nat.mul_le_mul_left (8 * K.M.n) (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this; omega
  · right; have := Nat.mul_le_mul_left (8 * K.M.n) (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this; omega

/-- A slot but the grid's is apart from grid slot `i`. -/
theorem JacWinLay.jg_apart (hL : JacWinLay K size) {x : Nat} (hx : x ∈ jwRo K ++ jwOther K) {i : Nat}
    (hi : i < 85) : x + 8 * K.M.n ≤ jg K i ∨ jg K i + 8 * K.M.n ≤ x := by
  have h85 : 8 * K.M.n * i + 8 * K.M.n ≤ 85 * (8 * K.M.n) := by
    rw [show 85 * (8 * K.M.n) = 8 * K.M.n * 85 from Nat.mul_comm _ _, ← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hi
  unfold jg
  rcases hL.tbl x hx with h | h
  · left; omega
  · right; omega

theorem JacWinLay.n0 (hL : JacWinLay K size) : 0 < K.M.n := by rw [hL.n4]; decide

theorem JacWinLay.jg_ne (hL : JacWinLay K size) {x : Nat} (hx : x ∈ jwRo K ++ jwOther K) {i : Nat}
    (hi : i < 85) : x ≠ jg K i := by
  have := hL.n0
  rcases hL.jg_apart hx hi with h | h <;> omega

/-- Two distinct slots are apart. -/
theorem JacWinLay.ap (hL : JacWinLay K size) {x y : Nat} (hx : x ∈ jwSlots K) (hy : y ∈ jwSlots K)
    (h : x ≠ y) : x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x :=
  hL.lay.apart x y hx hy h

/-- The other slots at distinct positions are distinct. -/
theorem JacWinLay.oth_ne (hL : JacWinLay K size) {i j : Nat} (hi : i < 13) (hj : j < 13) (h : i ≠ j) :
    (jwOther K)[i]'hi ≠ (jwOther K)[j]'hj := fun e => h (hL.nodup.getElem_inj.mp e)

theorem JacWinLay.le (hL : JacWinLay K size) {x : Nat} (hx : x ∈ jwSlots K) : x + 8 * K.M.n ≤ size :=
  hL.lay.le x hx

/-- `T` and its powers are grid slots `80 … 84`. -/
theorem JacWinLay.Tx (hL : JacWinLay K size) : K.E.x = jg K 80 := by
  show K.T = _; rw [hL.T]; unfold jg JacWinCfg.st; omega

theorem JacWinLay.Ty (hL : JacWinLay K size) : K.E.y = jg K 81 := by
  show K.T + 8 * K.M.n = _; rw [hL.T]; unfold jg JacWinCfg.st; omega

theorem JacWinLay.Tz (hL : JacWinLay K size) : K.E.z = jg K 82 := by
  show K.T + 16 * K.M.n = _; rw [hL.T]; unfold jg JacWinCfg.st; omega

theorem JacWinLay.Tz2 (hL : JacWinLay K size) : K.z2 = jg K 83 := by
  show K.T + 24 * K.M.n = _; rw [hL.T]; unfold jg JacWinCfg.st; omega

theorem JacWinLay.Tz3 (hL : JacWinLay K size) : K.z2 + 8 * K.M.n = jg K 84 := by
  show K.T + 24 * K.M.n + 8 * K.M.n = _; rw [hL.T]; unfold jg JacWinCfg.st; omega

theorem JacWinLay.T80 (hL : JacWinLay K size) : K.T = jg K 80 := hL.Tx

/-- Coordinate `c` of `T`. -/
theorem JacWinLay.Tc (hL : JacWinLay K size) (c : Nat) : K.T + 8 * K.M.n * c = jg K (80 + c) := by
  rw [hL.T]; unfold jg JacWinCfg.st; rw [Nat.mul_add]; omega

/-- Entry `m`'s address. -/
theorem entry_addr (K : JacWinCfg) (m c : Nat) :
    K.tbl + K.st * (m - 1) + 8 * K.M.n * c = jg K (5 * (m - 1) + c) := by
  unfold jg JacWinCfg.st
  rw [Nat.mul_add, show 40 * K.M.n * (m - 1) = 8 * K.M.n * (5 * (m - 1)) by
    rw [Nat.mul_assoc, Nat.mul_assoc, show 40 = 8 * 5 from rfl, Nat.mul_assoc, Nat.mul_left_comm 5]]
  omega

/-- The grid's region is in the working space. -/
theorem JacWinLay.grid_le (hL : JacWinLay K size) : K.tbl + 85 * (8 * K.M.n) ≤ size := by
  have := hL.le (jg_mem (K := K) (i := 84) (by decide))
  unfold jg at this; omega

/-- A slot read only is apart from what is written. -/
theorem JacWinLay.ro_w (hL : JacWinLay K size) {x : Nat} (hx : x ∈ jwRo K) :
    ∀ w ∈ jwW K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  simp only [jwW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · rcases List.mem_append.mp hy with hy | hy
    · exact hL.ap (ro_mem hx) (other_mem hy) fun e => hL.ro x hx (e ▸ hy)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      exact hL.jg_apart (List.mem_append_left _ hx) (List.mem_range.mp hi)
  · exact hL.lay.tmp x (ro_mem hx)

/-- What the loop writes is written. -/
theorem jwLoopW_sub (K : JacWinCfg) : ∀ w ∈ jwLoopW K, w ∈ jwW K := by
  intro w hw
  simp only [jwLoopW, jwW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · refine Or.inl ⟨y, ?_, rfl⟩
    rcases hy with hy | ⟨c, hc, rfl⟩
    · exact other_ws hy
    · exact jg_ws (by have := List.mem_range.mp hc; omega)
  · exact Or.inr rfl

/-- What is written misses the modulus. -/
theorem JacWinLay.w_mo (hL : JacWinLay K size) {m : Nat} {mem : Mem} {base : Addr}
    (hM : ModOkW K.M size m mem base) : ∀ w ∈ jwW K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  simp only [jwW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · have := hL.lay.mo y (ws_mem hy); dsimp only; omega
  · have := hM.sep; dsimp only; omega

end VG.Proof.Weierstrass.X86_64
