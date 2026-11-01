module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Tab
public import VerifiedGarbage.Proof.MillerRabin.Arm.Words
import VerifiedGarbage.Proof.Rsa.Arm.RvBase
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

/-! # The Miller–Rabin round on ARMv7: the windows

`wst P σ j`: `y` and the flag after `j` of the `16 w` windows (`mrun`).
`WI P m r`: in the word `m − 1` of `E` (`m` words left), `r` of its windows
left, the word shifted past the others (`svOf`); `WO P m`: `m` words left.
A window goes from `WI P m (n + 1)` to `WI P m n`, or `WO P (m − 1)` at the
word's end (`win_step`); a word from `WO P (n + 1)` to `WO P n` (`word_step`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- `y` and the flag after `j` windows. -/
abbrev wst (P : MP) (σ : State) (j : Nat) : Nat × Bool :=
  mrun (cOf P σ.mem) P.w (mOf P σ) (tv P σ) (eOf P σ) (16 * P.w) j

/-- The arrays during the windows. -/
def AW (P : MP) (j : Nat) (σ : State) (i : Nat) : Nat :=
  if i = aY then (wst P σ j).1 else if i = aM1 then mOf P σ else tv P σ (i - aT0)

/-- `y`, `−1` and the table. -/
abbrev LW : List Nat := [aY, aM1, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]

/-- The word `m − 1` of `E` shifted for `r` windows left. -/
abbrev svOf (P : MP) (σ : State) (m r : Nat) : Nat := (BitVec.ofNat 32 (ew P σ (m - 1)) <<< (4 * (8 - r))).toNat

/-- In the word `m − 1`, `r` of its windows left. -/
def WI (P : MP) (m r : Nat) (σ s : State) : Prop :=
  1 ≤ m ∧ m ≤ 2 * P.w ∧ r ≤ 8 ∧ St P (In P) (AW P (16 * P.w - (8 * (m - 1) + r))) LW
    (fun σ => upd (upd (upd (fun _ => 0) sF (wst P σ (16 * P.w - (8 * (m - 1) + r))).2.toNat) sK
      (8 * (m - 1) + r)) sV (svOf P σ m r)) [sV, sK, sF] σ s

/-- `m` words left. -/
def WO (P : MP) (m : Nat) (σ s : State) : Prop :=
  m ≤ 2 * P.w ∧ St P (In P) (AW P (16 * P.w - 8 * m)) LW
    (fun σ => upd (upd (fun _ => 0) sF (wst P σ (16 * P.w - 8 * m)).2.toNat) sK (8 * m)) [sK, sF] σ s

section
variable {P : MP} {σ : State}

theorem wst_lt (h : In P σ) (j : Nat) : (wst P σ j).1 < cOf P σ.mem := by
  have := h.c3
  cases j with
  | zero => exact tv_lt h 0
  | succ j => exact mm_lt (by omega_arith)

/-- The digit at the top of the shifted word is the window's. -/
theorem digit_sv (h : In P σ) {m r : Nat} (hm1 : 1 ≤ m) (hm : m ≤ 2 * P.w) (hr1 : 1 ≤ r) (hr : r ≤ 8) :
    digitOf (svOf P σ m r) = eOf P σ / 16 ^ (16 * P.w - 1 - (16 * P.w - (8 * (m - 1) + r))) % 16 := by
  have lt : ew P σ (m - 1) < 2 ^ 32 := (σ.mem.readW _ 32).isLt
  have e := shl_shr28 (BitVec.ofNat 32 (ew P σ (m - 1))) (t := 8 - r) (by omega_arith)
  rw [ofNat_toNat32 lt] at e
  have e2 : (BitVec.ofNat 32 (ew P σ (m - 1)) <<< (4 * (8 - r)) >>> 28).toNat = digitOf (svOf P σ m r) := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [← e2, e, h.ew_val (by omega_arith), show 28 - 4 * (8 - r) = 4 * (r - 1) by omega_arith, digit_word _ _ _ (by omega_arith),
    show 16 * P.w - 1 - (16 * P.w - (8 * (m - 1) + r)) = 8 * (m - 1) + (r - 1) by omega_arith]

theorem svOf_next {m n : Nat} (hn : n < 8) :
    (BitVec.ofNat 32 (svOf P σ m (n + 1)) <<< 4).toNat = svOf P σ m n := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, shl4_succ32, show 8 - (n + 1) + 1 = 8 - n by omega_arith]

theorem svOf_lt (m r : Nat) : svOf P σ m r < 2 ^ 32 := BitVec.isLt _

theorem svOf_eight (m : Nat) : svOf P σ m 8 = ew P σ (m - 1) := by
  rw [svOf, show 4 * (8 - 8) = 0 from rfl, BitVec.shiftLeft_zero, ofNat_toNat32 (σ.mem.readW _ 32).isLt]

end


/-! ## A window's stages, `n + 1` windows left in the word `m − 1` -/

section
variable (P : MP) (m n : Nat)

/-- The windows done. -/
abbrev jw : Nat := 16 * P.w - (8 * (m - 1) + (n + 1))

/-- The header words at the window's start. -/
def V0w (σ : State) : Nat → Nat :=
  upd (upd (upd (fun _ => 0) sF (wst P σ (jw P m n)).2.toNat) sK (8 * (m - 1) + (n + 1))) sV (svOf P σ m (n + 1))

/-- After the four squarings. -/
abbrev st4 (σ : State) : Nat × Bool := sqst P 4 (fun _ => 0) (fun σ => wst P σ (jw P m n)) σ 4
def A2w (σ : State) : Nat → Nat := upd (AW P (jw P m n) σ) aY (st4 P m n σ).1
def V2w (σ : State) : Nat → Nat := upd (upd (upd (V0w P m n σ) sR 0) sF (st4 P m n σ).2.toNat) sQ 0

/-- The digit, and after the scan, `−1` and the product. -/
abbrev dgw (σ : State) : Nat := digitOf (svOf P σ m (n + 1))
def A3w (σ : State) : Nat → Nat := upd (A2w P m n σ) aX (tv P σ (dgw P m n σ))
def A4w (σ : State) : Nat → Nat := upd (A3w P m n σ) aM1 (mOf P σ)
abbrev Y5w (σ : State) : Nat := mm (cOf P σ.mem) P.w (st4 P m n σ).1 (tv P σ (dgw P m n σ))
def A5w (σ : State) : Nat → Nat := upd (A4w P m n σ) aY (Y5w P m n σ)

/-- After the comparisons. -/
def V7w (σ : State) : Nat → Nat :=
  upd (upd (V2w P m n σ) sE1 (decide (Y5w P m n σ = tv P σ 0)).toNat) sE2 (decide (Y5w P m n σ = mOf P σ)).toNat

end

/-- The table's entries. -/
abbrev Lt : List Nat := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
abbrev LS4 : List Nat := [sQ, sR, sV, sK, sF]

theorem ite_toNat (p : Prop) [Decidable p] : (if p then 1 else 0) = (decide p).toNat := by
  by_cases h : p <;> simp [h]

theorem Lt_ne : ∀ i ∈ Lt, i ≠ aY ∧ i ≠ aX ∧ i ≠ aM1 := by decide

theorem AW_tab {P : MP} {j : Nat} {σ : State} {i : Nat} (hi : i ∈ Lt) : AW P j σ i = tv P σ (i - aT0) := by
  obtain ⟨h1, -, h3⟩ := Lt_ne i hi
  unfold AW; rw [ite_eq_right h1, ite_eq_right h3]

section
variable {P : MP} {m n : Nat} {σ : State}

theorem A5w_Y : A5w P m n σ aY = Y5w P m n σ := upd_self _ _ _
theorem A5w_M : A5w P m n σ aM1 = mOf P σ := by
  unfold A5w A4w; rw [upd_ne _ _ (by decide), upd_self]
theorem A5w_tab {i : Nat} (hi : i ∈ Lt) : A5w P m n σ i = tv P σ (i - aT0) := by
  obtain ⟨h1, h2, h3⟩ := Lt_ne i hi
  unfold A5w A4w A3w A2w; rw [upd_ne _ _ h1, upd_ne _ _ h3, upd_ne _ _ h2, upd_ne _ _ h1, AW_tab hi]
theorem A4w_Y : A4w P m n σ aY = (st4 P m n σ).1 := by
  unfold A4w A3w A2w; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]
theorem A4w_X : A4w P m n σ aX = tv P σ (dgw P m n σ) := by
  unfold A4w A3w; rw [upd_ne _ _ (by decide), upd_self]
theorem dgw_lt : dgw P m n σ < 16 := by
  have := svOf_lt (P := P) (σ := σ) m (n + 1); unfold dgw digitOf; omega_arith

theorem V2w_sV : V2w P m n σ sV = svOf P σ m (n + 1) := by
  unfold V2w V0w; simp only [upd, show sV ≠ sQ by decide, show sV ≠ sF by decide, show sV ≠ sR by decide, ↓reduceIte]
theorem V7w_sV : V7w P m n σ sV = svOf P σ m (n + 1) := by
  unfold V7w; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), V2w_sV]
theorem V7w_sE1 : V7w P m n σ sE1 = (decide (Y5w P m n σ = tv P σ 0)).toNat := by
  unfold V7w; rw [upd_ne _ _ (by decide), upd_self]
theorem V7w_sE2 : V7w P m n σ sE2 = (decide (Y5w P m n σ = mOf P σ)).toNat := by
  unfold V7w; rw [upd_self]
theorem V7w_sF : V7w P m n σ sF = (st4 P m n σ).2.toNat := by
  unfold V7w V2w; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]
theorem V7w_sK : V7w P m n σ sK = 8 * (m - 1) + (n + 1) := by
  unfold V7w V2w V0w
  simp only [upd, show sK ≠ sE2 by decide, show sK ≠ sE1 by decide, show sK ≠ sQ by decide, show sK ≠ sF by decide,
    show sK ≠ sR by decide, show sK ≠ sV by decide, ↓reduceIte]

/-- The window's result. -/
theorem wst_next (h : In P σ) (hm1 : 1 ≤ m) (hm : m ≤ 2 * P.w) (hn : n + 1 ≤ 8) :
    wst P σ (jw P m n + 1) = (Y5w P m n σ, if dgw P m n σ = 0 then (st4 P m n σ).2 else
      (decide (Y5w P m n σ = tv P σ 0) || decide (Y5w P m n σ = mOf P σ))) := by
  have hd := digit_sv h hm1 hm (by omega_arith) hn
  show mwin _ _ _ _ (eOf P σ / 16 ^ (16 * P.w - 1 - jw P m n) % 16) (wst P σ (jw P m n)) = _
  rw [← hd]
  rfl

end

/-- One window. -/
theorem win_step {P : MP} {m : Nat} (n : Nat) (fios : Bool := false) :
    VP (WI P m (n + 1)) (win (fios := fios)) fun σ s =>
      isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → WO P (m - 1) σ s) ∧ (0 < n → WI P m n σ s) := by
  by_cases hc : 1 ≤ m ∧ m ≤ 2 * P.w ∧ n + 1 ≤ 8
  swap
  · exact VP.of_false fun σ s h => hc ⟨h.1, h.2.1, h.2.2.1⟩
  obtain ⟨hm1, hm, hn⟩ := hc
  refine VP.of_imp (p := P.w ≤ 128) (fun σ s h => (h.2.2.2.1 : In P σ).w128) fun w128 => ?_
  refine VP.mono (F := St P (In P) (AW P (jw P m n)) LW (V0w P m n) [sV, sK, sF]) ?_ (fun σ s h => h.2.2.2)
    (fun _ _ h => h)
  simp only [win, seqs]
  -- The count and threshold of the squarings.
  refine VP.seq (G := SqS P (In P) (AW P (jw P m n)) LW.tail (fun σ => upd (V0w P m n σ) sR 0) LS4 4 (fun _ => 0)
    (fun σ => wst P σ (jw P m n)) 4) ?_ ?_
  · refine St.psqFour.mono (fun _ _ h => h) fun σ s h => ⟨Nat.le_refl _, h.mono (fun i hi => ⟨hi, ?_⟩)
      (fun d hd => ⟨hd, ?_⟩)⟩
    · rcases List.mem_cons.mp hi with rfl | hi
      · show AW P (jw P m n) σ aY = upd (AW P (jw P m n) σ) aY (wst P σ (jw P m n)).1 aY
        rw [upd_self]; rfl
      · exact (upd_ne _ _ ((by decide : ∀ i ∈ LW.tail, i ≠ aY) i hi)).symm
    · simp only [LS4, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> rfl
  -- The squarings.
  refine VP.seq (G := St P (In P) (A2w P m n) (aY :: LW.tail) (V2w P m n) LS4)
    ((sq_loop (fios := fios) (fun σ e => e) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (fun σ _ => rfl) (fun σ _ => upd_self _ _ _)
      (fun _ _ => by decide) (by decide) (fun σ e => wst_lt e _) 3).mono (fun _ _ h => h)
      (fun σ s h => h.2)) ?_
  -- The scan.
  refine VP.seq (G := St P (In P) (A3w P m n) (aX :: aY :: Lt) (V2w P m n) LS4) ?_ ?_
  · refine VP.mono (F := St P (In P) (A2w P m n) (aY :: Lt) (V2w P m n) LS4) ?_ (fun σ s h => ?_)
      (fun _ _ h => h)
    · refine (St.pscan (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun σ _ => by rw [V2w_sV]; exact svOf_lt m (n + 1))).mono (fun _ _ h => h) fun σ s h => ?_
      refine h.mono (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
      rw [V2w_sV]
      show upd _ aX (A2w P m n σ (aT0 + dgw P m n σ)) i = upd _ aX (tv P σ (dgw P m n σ)) i
      have dl : dgw P m n σ < 16 := dgw_lt
      congr 1
      unfold A2w
      rw [upd_ne _ _ (by simp only [aT0, aY]; omega_arith), AW_tab (i := aT0 + dgw P m n σ) (by
        have : ∀ k < 16, aT0 + k ∈ Lt := by decide
        exact this _ dl), Nat.add_sub_cancel_left]
    · exact h.mono (fun i hi => ⟨(by decide : ∀ i ∈ aY :: Lt, i ∈ aY :: LW.tail) i hi, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩)
  -- `−1`.
  refine VP.seq (G := St P (In P) (A4w P m n) (aM1 :: aX :: aY :: Lt) (V2w P m n) LS4)
    (St.pcopyClr cM1_taint (by decide) (by decide) (by decide) (by decide)) ?_
  -- `y T_d`.
  refine VP.seq (G := St P (In P) (A5w P m n) (aY :: aM1 :: aX :: Lt) (V2w P m n) LS4) ?_ ?_
  · refine VP.mono (F := St P (In P) (A4w P m n) (aY :: aM1 :: aX :: Lt) (V2w P m n) LS4) ?_ (fun σ s h => ?_)
      (fun _ _ h => h)
    · refine (St.pmulY (fios := fios) (.inr rfl) (by decide) (by decide) (by decide) (by decide)
        (fun σ e => by rw [A4w_Y]; exact sqst_lt (q0 := 4) (fun σ e => e) (fun σ e => wst_lt e _) σ e 4)
        (fun σ e => by rw [A4w_X]; exact tv_lt e _)).mono (fun _ _ h => h) fun σ s h => ?_
      refine h.mono (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
      rw [A4w_Y, A4w_X]; rfl
    · exact h.mono (fun i hi => ⟨(by decide : ∀ i ∈ aY :: aM1 :: aX :: Lt, i ∈ aM1 :: aX :: aY :: Lt) i hi, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩)
  -- The comparisons.
  refine VP.seq (G := St P (In P) (A5w P m n) (aY :: aM1 :: Lt)
    (fun σ => upd (V2w P m n σ) sE1 (decide (Y5w P m n σ = tv P σ 0)).toNat) (sE1 :: LS4)) ?_ ?_
  · refine VP.mono (F := St P (In P) (A5w P m n) (aY :: aM1 :: Lt) (V2w P m n) LS4) ?_ (fun σ s h => ?_)
      (fun _ _ h => h)
    · refine (St.peqS eq1_taint (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).mono (fun _ _ h => h) fun σ s h => h.mono (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨hd, ?_⟩)
      rw [A5w_Y, A5w_tab (i := aT0) (by decide), ite_toNat, Nat.sub_self]
    · exact h.mono (fun i hi => ⟨(by decide : ∀ i ∈ aY :: aM1 :: Lt, i ∈ aY :: aM1 :: aX :: Lt) i hi, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩)
  refine VP.seq (G := St P (In P) (A5w P m n) (aY :: aM1 :: Lt) (V7w P m n) (sE2 :: sE1 :: LS4))
    ((St.peqS eq2_taint (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).mono (fun _ _ h => h) fun σ s h => h.mono (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨hd, ?_⟩)) ?_
  · rw [A5w_Y, A5w_M, ite_toNat]; rfl
  -- The flag, the word and the count.
  refine (St.pwinEnd (K := 8 * (m - 1) + n) (v := fun σ => svOf P σ m (n + 1))
    (e1 := fun σ => decide (Y5w P m n σ = tv P σ 0)) (e2 := fun σ => decide (Y5w P m n σ = mOf P σ))
    (fb := fun σ => (st4 P m n σ).2) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun σ _ => V7w_sV) (fun σ _ => svOf_lt m (n + 1)) (fun σ _ => V7w_sE1) (fun σ _ => V7w_sE2)
    (fun σ _ => V7w_sF) (fun σ _ => V7w_sK) (by omega_arith)).mono (fun _ _ h => h) fun σ s ⟨h, z⟩ => ?_
  have pre : In P σ := h.1
  have wn := wst_next pre hm1 hm hn
  have j1 : jw P m n + 1 = 16 * P.w - (8 * (m - 1) + n) := by have := pre.w4; simp only [jw]; omega_arith
  rw [j1] at wn
  have hA : ∀ i ∈ LW, A5w P m n σ i = AW P (16 * P.w - (8 * (m - 1) + n)) σ i := fun i hi => by
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [A5w_Y]; unfold AW; rw [ite_eq_left rfl, wn]
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [A5w_M]; unfold AW; rw [ite_eq_right (by decide), ite_eq_left rfl]
    · rw [A5w_tab hi, AW_tab hi]
  have hF : (if digitOf (svOf P σ m (n + 1)) = 0 then (st4 P m n σ).2 else
      (decide (Y5w P m n σ = tv P σ 0) || decide (Y5w P m n σ = mOf P σ))).toNat =
      (wst P σ (16 * P.w - (8 * (m - 1) + n))).2.toNat := by rw [wn]
  have hL : ∀ i ∈ LW, i ∈ aY :: aM1 :: Lt := by decide
  have stI : 0 < n → WI P m n σ s := fun hn0 => by
    refine ⟨hm1, hm, by omega_arith, h.mono (fun i hi => ⟨hL i hi, hA i hi⟩) (fun d hd => ⟨?_, ?_⟩)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; rcases hd with rfl | rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · simp only [upd, show sV ≠ sK by decide, ↓reduceIte]; exact svOf_next (by omega_arith)
      · rw [upd_self, upd_ne _ _ (by decide : sK ≠ sV), upd_self]
      · simp only [upd, show sF ≠ sK by decide, show sF ≠ sV by decide, ↓reduceIte]; exact hF
  have stO : n = 0 → WO P (m - 1) σ s := fun hn0 => by
    subst hn0
    refine ⟨by omega_arith, h.mono (fun i hi => ⟨hL i hi, ?_⟩) (fun d hd => ⟨?_, ?_⟩)⟩
    · rw [hA i hi, show 16 * P.w - (8 * (m - 1) + 0) = 16 * P.w - 8 * (m - 1) by omega_arith]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; rcases hd with rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · simp only [upd_self, Nat.add_zero]
      · simp only [upd, show sF ≠ sK by decide, show sF ≠ sV by decide, ↓reduceIte]
        rw [hF, show 16 * P.w - (8 * (m - 1) + 0) = 16 * P.w - 8 * (m - 1) by omega_arith]
  refine ⟨?_, stO, stI⟩
  show some (!s.z) = _
  rw [z]
  by_cases h0 : n = 0
  · subst h0; simp
  · have : (8 * (m - 1) + n) % 8 = n := by omega_arith
    rw [this]; simp [h0]; omega_arith

end VG.Proof.MillerRabin.Arm

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

/-- A word's windows. -/
theorem word_step {P : MP} (n : Nat) (fios : Bool := false) :
    VP (WO P (n + 1)) (word (fios := fios)) fun σ s =>
      isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → WO P 0 σ s) ∧ (0 < n → WO P n σ s) := by
  by_cases hc : n + 1 ≤ 2 * P.w
  swap
  · exact VP.of_false fun σ s h => hc h.1
  refine VP.of_imp (p := P.w ≤ 128) (fun σ s h => (h.2.1 : In P σ).w128) fun w128 => ?_
  refine VP.mono (F := St P (In P) (AW P (16 * P.w - 8 * (n + 1))) LW
    (fun σ => upd (upd (fun _ => 0) sF (wst P σ (16 * P.w - 8 * (n + 1))).2.toNat) sK (8 * (n + 1))) [sK, sF]) ?_
    (fun σ s h => h.2) (fun _ _ h => h)
  simp only [Impl.MillerRabin.Arm.word, seqs]
  refine VP.seq (St.pwordK (K := 8 * (n + 1)) (by decide) (fun σ _ => by
    rw [upd_self])) (VP.seq (St.pwordLd (m := n + 1) (fun σ e => e) (by omega_arith) hc) ?_)
  refine VP.seq ((VP.loop (I := fun k => WI P (n + 1) k) (fun k => win_step (fios := fios) k) 7).mono (fun σ s h => ?_)
    (fun _ _ h => h)) ?_
  · refine ⟨by omega_arith, hc, by decide, ?_⟩
    refine h.mono (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨?_, ?_⟩)
    · rw [show 16 * P.w - (8 * (n + 1 - 1) + 8) = 16 * P.w - 8 * (n + 1) by omega_arith]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; rcases hd with rfl | rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · rw [upd_self, upd_self, svOf_eight, Nat.add_sub_cancel]
      · rw [upd_ne _ _ (by decide), upd_self, upd_ne _ _ (by decide), upd_self]; omega_arith
      · simp only [upd, show sF ≠ sV by decide, show sF ≠ sK by decide, ↓reduceIte]
        rw [show 16 * P.w - (8 * (n + 1 - 1) + (7 + 1)) = 16 * P.w - 8 * (n + 1) by omega_arith]
  · refine VP.mono (F := St P (In P) (AW P (16 * P.w - 8 * n)) LW
      (fun σ => upd (upd (fun _ => 0) sF (wst P σ (16 * P.w - 8 * n)).2.toNat) sK (8 * n)) [sK, sF]) ?_
      (fun σ s h => by rw [Nat.add_sub_cancel] at h; exact h.2) (fun _ _ h => h)
    refine (St.pwordEnd (K := 8 * n) (by decide) (fun σ _ => upd_self _ _ _) (by omega_arith)).mono (fun _ _ h => h)
      fun σ s ⟨h, z⟩ => ⟨?_, fun h0 => ⟨by omega_arith, h0 ▸ h⟩, fun _ => ⟨by omega_arith, h⟩⟩
    show some (!s.z) = _
    rw [z]
    by_cases h0 : n = 0 <;> simp [h0, Nat.pos_iff_ne_zero, Nat.mul_eq_zero]

/-- The words. -/
theorem words_loop {P : MP} (fios : Bool := false) : VP (WO P (2 * P.w)) (.loop (word (fios := fios)) .ne) (WO P 0) := by
  refine VP.of_imp (p := 1 ≤ P.w) (fun σ s h => by have := (h.2.1 : In P σ).w4; omega_arith) fun w1 => ?_
  have := VP.loop (I := fun k => WO P k) (fun k => word_step (fios := fios) k) (2 * P.w - 1)
  rwa [show 2 * P.w - 1 + 1 = 2 * P.w by omega_arith] at this

end VG.Proof.MillerRabin.Arm
