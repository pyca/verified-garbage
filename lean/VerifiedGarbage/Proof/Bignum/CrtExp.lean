import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA with the CRT: the exponentiation in a prime's workspace

In a prime's workspace (`X`, `w_X` words, `R = 2^(64 w_X)`), with
`Y ≡ R` and `[aXc] ≡ x R`, the table `T_j ≡ x^j R` after the arrays
(`CTab`, entry `j` the array `8 + j`: `ent_le`), and windows of 4 bits:
`Y := Y¹⁶ T_v R⁻¹` (`mont_mulT`, `win_step`). These are the facts about it
that do not depend on the target, with what each part of it changes
(`crtWinRanges`, `crtExpRanges`, `selRanges`, `buildRanges`).
-/

namespace VG.Proof.Bignum

open VG VG.Impl.Bignum VG.Impl.Bignum.Public

theorem slot_mono (w : Nat) {j k : Nat} (h : j ≤ k) : slot w j ≤ slot w k := by
  unfold slot; have := Nat.mul_le_mul_right (8 * (w + 2)) h; omega_arith

/-- Entry `j` of the table is the workspace's array `8 + j`. -/
theorem ent_le (wx : Nat) {j : Nat} (hj : j < 16) :
    slot wx (8 + j) + 8 * (wx + 2) ≤ slot wx 8 + tabBytes wx := by
  have := Nat.mul_le_mul_right (8 * (wx + 2)) (show 8 + j + 1 ≤ 24 by omega_arith)
  unfold slot tabBytes
  rw [Nat.add_mul, Nat.one_mul] at this
  omega_arith

/-- What a window of the exponentiation changes in the prime's workspace:
arrays and header slots. -/
def crtWinRanges (wx : Nat) : List (Nat × Nat) :=
  [(slot wx aAcc, 8 * (wx + 2)), (slot wx aTmp, 8 * (wx + 2)), (slot wx aY, 8 * (wx + 2)),
    (slot wx Crt.aT, 8 * (wx + 2)), (8 * Crt.sV, 8), (8 * Crt.sBit, 8), (8 * Crt.sNib, 8), (8 * Crt.sEnt, 8),
    (8 * Crt.sJ, 8)]

/-- What the exponentiation changes: also the exponent's pointer and length,
the byte index, and the table. -/
def crtExpRanges (wx : Nat) : List (Nat × Nat) :=
  (8 * Crt.sExp, 8) :: (8 * Crt.sExpLen, 8) :: (8 * Crt.sI, 8) :: (8 * Crt.sTab, 8) ::
    (slot wx 8, tabBytes wx) :: crtWinRanges wx

theorem crtWinRanges_sub (wx : Nat) : ∀ r ∈ crtWinRanges wx, r ∈ crtExpRanges wx := fun _ hr =>
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ hr))))

theorem crtWinRanges_ok (wx : Nat) : ∀ r ∈ crtWinRanges wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 := by
  have := hdr_lt_slot wx 0 (show 31 < 32 by decide)
  have := slot_le (w := wx) (show aAcc < 8 by decide)
  have := slot_le (w := wx) (show aTmp < 8 by decide)
  have := slot_le (w := wx) (show aY < 8 by decide)
  have := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have h1 : slot wx 0 ≤ slot wx aAcc := slot_mono wx (by decide)
  have h2 : slot wx 0 ≤ slot wx aTmp := slot_mono wx (by decide)
  have h3 : slot wx 0 ≤ slot wx aY := slot_mono wx (by decide)
  have h4 : slot wx 0 ≤ slot wx Crt.aT := slot_mono wx (by decide)
  simp only [crtWinRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [Crt.sV, Crt.sBit, Crt.sNib, Crt.sEnt, Crt.sJ, sFn] at * <;> omega_arith

theorem crtExpRanges_ok (wx : Nat) :
    ∀ r ∈ crtExpRanges wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + tabBytes wx := by
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  intro r hr
  simp only [crtExpRanges, List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | hr
  · simp only [Crt.sExp, sFn]; omega_arith
  · simp only [Crt.sExpLen, sFn]; omega_arith
  · simp only [Crt.sI, sFn]; omega_arith
  · simp only [Crt.sTab, sFn]; omega_arith
  · simp only; omega_arith
  · have := crtWinRanges_ok wx r hr; omega_arith

/-- The arrays the exponentiation does not change. -/
theorem crtExpRanges_arr (wx : Nat) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aY)
    (h4 : j ≠ Crt.aT) : ∀ r ∈ crtExpRanges wx, slot wx j + 8 * (wx + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot wx j := by
  have := hdr_lt_slot wx j (show 31 < 32 by decide)
  have s1 := slot_sep (w := wx) h1
  have s2 := slot_sep (w := wx) h2
  have s3 := slot_sep (w := wx) h3
  have s4 := slot_sep (w := wx) h4
  have s8 := slot_le (w := wx) hj
  simp only [crtExpRanges, crtWinRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [Crt.sExp, Crt.sExpLen, Crt.sI, Crt.sTab, Crt.sV, Crt.sBit, Crt.sNib, Crt.sEnt, Crt.sJ, sFn] at * <;>
    omega_arith

/-- A header slot that a window does not change. -/
theorem crtWinRanges_hdr (wx : Nat) {k : Nat} (hk : k < 32) (h1 : k ≠ Crt.sV) (h2 : k ≠ Crt.sBit)
    (h3 : k ≠ Crt.sNib) (h4 : k ≠ Crt.sEnt) (h5 : k ≠ Crt.sJ) :
    ∀ r ∈ crtWinRanges wx, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  have := hdr_lt_slot wx aAcc hk
  have := hdr_lt_slot wx aTmp hk
  have := hdr_lt_slot wx aY hk
  have := hdr_lt_slot wx Crt.aT hk
  simp only [crtWinRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [Crt.sV, Crt.sBit, Crt.sNib, Crt.sEnt, Crt.sJ, sFn] at * <;> omega_arith

/-- The table's entries are past what a window changes. -/
theorem crtWinRanges_ent (wx : Nat) (j : Nat) :
    ∀ r ∈ crtWinRanges wx, slot wx (8 + j) + 8 * (wx + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot wx (8 + j) :=
  fun r hr => Or.inr (by have := (crtWinRanges_ok wx r hr).2; have := slot_mono wx (show 8 ≤ 8 + j by omega_arith); omega_arith)

/-- The table: `T_j < X`, and `T_j ≡ x^j R` if `Q`; its first entry's
address in `sTab`. -/
structure CTab (m : Mem) (P : Addr) (wx X : Nat) (Q : Prop) (x : Nat) : Prop where
  tab : word m P (8 * Crt.sTab) = off P (slot wx 8)
  lt : ∀ j < 16, wv m P (slot wx (8 + j)) wx < X
  val : Q → ∀ j < 16, wv m P (slot wx (8 + j)) wx % X = x ^ j * 2 ^ (64 * wx) % X

theorem CTab.of_win {m m' : Mem} {P : Addr} {wx X : Nat} {Q : Prop} {x : Nat} (h : CTab m P wx X Q x)
    (hf : Frm P (crtWinRanges wx) m m') (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) :
    CTab m' P wx X Q x := by
  have he : ∀ j < 16, wv m' P (slot wx (8 + j)) wx = wv m P (slot wx (8 + j)) wx := fun j hj =>
    hf.wv_eq (fun r hr => by have := crtWinRanges_ent wx j r hr; omega_arith) (by have := ent_le wx hj; omega_arith)
  refine ⟨?_, fun j hj => (he j hj).symm ▸ h.lt j hj, fun hQ j hj => (he j hj).symm ▸ h.val hQ j hj⟩
  rw [hf.word_eq (crtWinRanges_hdr wx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by have := hdr_lt_slot wx 8 (show Crt.sTab < 32 by decide); omega_arith)]
  exact h.tab

theorem xor_eq_zero_iff {x y : BitVec 64} : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    have := congrArg (· ^^^ y) h
    simpa [BitVec.xor_assoc] using this
  · rintro rfl
    simp

theorem ofNat64_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · rintro rfl; rfl

theorem slot_succ (w k : Nat) : slot w (k + 1) = slot w k + 8 * (w + 2) := by
  unfold slot; rw [Nat.succ_mul]; omega_arith

/-- What the selection changes: `T`, the entry and its index. -/
def selRanges (wx : Nat) : List (Nat × Nat) :=
  [(slot wx Crt.aT, 8 * (wx + 2)), (8 * Crt.sEnt, 8), (8 * Crt.sJ, 8)]

theorem selRanges_sub (wx : Nat) : ∀ r ∈ selRanges wx, r ∈ crtWinRanges wx := by
  simp only [selRanges, crtWinRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> simp

/-- A Montgomery product of `Y ≡ x^E R` and `T ≡ x^v R`: `x^(E+v) R`. -/
theorem mont_mulT {Y Y' T x E v R m : Nat} (hR : Nat.Coprime R m) (hY : Y % m = x ^ E * R % m)
    (hT : T % m = x ^ v * R % m) (h : Y' * R % m = Y * T % m) : Y' % m = x ^ (E + v) * R % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, Nat.mul_mod, hY, hT, ← Nat.mul_mod, Nat.pow_add]
  congr 1
  grind

theorem win_step {E v j : Nat} (hv : v < 256) (hj : j < 2) :
    16 * (E * 16 ^ j + v / 16 ^ (2 - j)) + v * 16 ^ j / 16 % 16 = E * 16 ^ (j + 1) + v / 16 ^ (2 - (j + 1)) := by
  rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl <;> simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd] <;>
    omega_arith

/-- What the table's build changes: the products' arrays, its slots and the table. -/
def buildRanges (wx : Nat) : List (Nat × Nat) :=
  [(slot wx aAcc, 8 * (wx + 2)), (slot wx aTmp, 8 * (wx + 2)), (slot wx Crt.aT, 8 * (wx + 2)),
    (8 * Crt.sTab, 8), (8 * Crt.sEnt, 8), (8 * Crt.sBit, 8), (slot wx 8, tabBytes wx)]

theorem buildRanges_sub (wx : Nat) : ∀ r ∈ buildRanges wx, r ∈ crtExpRanges wx := by
  simp only [buildRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [crtExpRanges, crtWinRanges]

/-- `Y` is past what the build changes. -/
theorem buildRanges_y (wx : Nat) :
    ∀ r ∈ buildRanges wx, slot wx aY + 8 * wx ≤ r.1 ∨ r.1 + r.2 ≤ slot wx aY := by
  have := hdr_lt_slot wx aY (show 31 < 32 by decide)
  have s1 := slot_sep (w := wx) (show aY ≠ aAcc by decide)
  have s2 := slot_sep (w := wx) (show aY ≠ aTmp by decide)
  have s3 := slot_sep (w := wx) (show aY ≠ Crt.aT by decide)
  have s8 := slot_le (w := wx) (show aY < 8 by decide)
  simp only [buildRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [Crt.sTab, Crt.sEnt, Crt.sBit, sFn] at * <;> omega_arith

end VG.Proof.Bignum
