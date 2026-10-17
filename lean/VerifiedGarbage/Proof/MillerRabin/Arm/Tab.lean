module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Sq
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The Miller–Rabin round on ARMv7: the table

`tv P σ k`: the table's entry `k`, `x^k` in Montgomery form (`tp`). `TS P k`:
the table's loop with `k` of its 14 iterations left, after `i = 14 − k`: `y`
is `tv (i + 1)`, entries 0 and 1 are `1` and `x`, and entry `k ≥ 2` is
`tv (k + i − 14)` once shifted in (`k + i > 15`), else the original array
`k + i` (`AT`). From the body's start (`tab_init`) to the loop's end
(`tab_loop`), where every entry is `tv k`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Spec.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- The table's entry `k`. -/
abbrev tv (P : MP) (σ : State) (k : Nat) : Nat := tp (cOf P σ.mem) P.w (xOf P σ) (oOf P σ) k

/-- Entry `k` of the table after `i` iterations. -/
def tabEnt (P : MP) (σ : State) (i k : Nat) : Nat :=
  if k = 0 then oOf P σ else if k = 1 then xOf P σ else
    if k + i ≤ 15 then num σ.mem P.B P.W (aT0 + (k + i)) else tv P σ (k + i - 14)

/-- The arrays after `i` iterations. -/
def AT (P : MP) (i : Nat) (σ : State) (j : Nat) : Nat :=
  if j = aY then tv P σ (i + 1) else if j = aX then xOf P σ else tabEnt P σ i (j - aT0)

/-- `y`, `x` and the table. -/
abbrev LT : List Nat := [aY, aX, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]

/-- The table's loop with `k` iterations left. -/
def TS (P : MP) (k : Nat) (σ s : State) : Prop :=
  k ≤ 14 ∧ St P (In P) (AT P (14 - k)) LT (fun _ => upd (fun _ => 0) sK k) [sK] σ s

theorem LT_tab : ∀ k < 16, aT0 + k ∈ LT := by decide

theorem tv_lt {P : MP} {σ : State} (h : In P σ) (k : Nat) : tv P σ k < cOf P σ.mem := by
  have := h.c3
  exact tp_lt (by omega) h.x5 (by show numAt σ.mem (State.addr P.ws) P.w 9 < _; rw [h.one]; exact Nat.mod_lt _ (by omega)) k

/-- An iteration's arrays: `y := y x`, then the shift. -/
theorem AT_step {P : MP} {σ : State} {i : Nat} (hi : i < 14) :
    ∀ j ∈ LT, shiftArr (upd (AT P i σ) aY (mm (cOf P σ.mem) P.w (AT P i σ aY) (AT P i σ aX))) 2 j =
      AT P (i + 1) σ j := by
  have ey : mm (cOf P σ.mem) P.w (AT P i σ aY) (AT P i σ aX) = tv P σ (i + 2) := rfl
  rw [ey]
  have mid : ∀ k, 2 ≤ k → k ≤ 14 →
      shiftArr (upd (AT P i σ) aY (tv P σ (i + 2))) 2 (aT0 + k) = AT P (i + 1) σ (aT0 + k) := by
    intro k h1 h2
    unfold shiftArr AT upd tabEnt
    have e0 : aT0 = 11 := rfl
    have e6 : aY = 6 := rfl
    have e5 : aX = 5 := rfl
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right, Nat.add_sub_cancel_left,
      show aT0 + k + 1 - aT0 = k + 1 by omega, show k + 1 + i = k + (i + 1) by omega]
  intro j hj
  simp only [LT, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact mid 2 (by decide) (by decide)
  · exact mid 3 (by decide) (by decide)
  · exact mid 4 (by decide) (by decide)
  · exact mid 5 (by decide) (by decide)
  · exact mid 6 (by decide) (by decide)
  · exact mid 7 (by decide) (by decide)
  · exact mid 8 (by decide) (by decide)
  · exact mid 9 (by decide) (by decide)
  · exact mid 10 (by decide) (by decide)
  · exact mid 11 (by decide) (by decide)
  · exact mid 12 (by decide) (by decide)
  · exact mid 13 (by decide) (by decide)
  · exact mid 14 (by decide) (by decide)
  · show shiftArr _ 2 (aT0 + 15) = AT P (i + 1) σ (aT0 + 15)
    unfold shiftArr AT upd tabEnt
    have e0 : aT0 = 11 := rfl
    have e6 : aY = 6 := rfl
    have e5 : aX = 5 := rfl
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right, Nat.add_sub_cancel_left]
    congr 1
    omega

/-- An iteration of the table's loop. -/
theorem tab_step {P : MP} (n : Nat) :
    VP (TS P (n + 1)) tabStep fun σ s =>
      isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → TS P 0 σ s) ∧ (0 < n → TS P n σ s) := by
  by_cases hn : n + 1 ≤ 14
  swap
  · exact VP.of_false fun σ s h => hn h.1
  obtain ⟨i, hi⟩ : ∃ i, i = 14 - (n + 1) := ⟨_, rfl⟩
  refine VP.mono (F := St P (In P) (AT P i) LT (fun _ => upd (fun _ => 0) sK (n + 1)) [sK]) ?_
    (fun σ s h => hi ▸ h.2) (fun _ _ h => h)
  simp only [tabStep, seqs]
  refine VP.seq (St.pmulY (L := LT.tail) (.inr rfl) (by decide) (by decide) (by decide) (by decide)
    (fun σ e => tv_lt e _) (fun σ e => e.x5)) (VP.seq (St.pshift LT_tab (by decide)) ?_)
  refine (St.pcnt (n := n) List.mem_cons_self (fun σ _ => upd_self _ _ _) (by omega)).mono (fun _ _ h => h)
    fun σ s ⟨h, z⟩ => ?_
  have ts : TS P n σ s := by
    refine ⟨by omega, h.mono (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨by simp only [List.mem_singleton] at hd; simp [hd],
      by simp only [List.mem_singleton] at hd; subst hd; simp only [upd_self]⟩)⟩
    rw [show 14 - n = i + 1 by omega]
    exact AT_step (by omega) j hj
  refine ⟨?_, fun h0 => h0 ▸ ts, fun _ => ts⟩
  show some (!s.z) = _
  rw [z]
  by_cases h0 : n = 0 <;> simp [h0] <;> omega

/-- The table's loop. -/
theorem tab_loop {P : MP} : VP (TS P 14) (.loop tabStep .ne) (TS P 0) := VP.loop (fun n => tab_step n) 13

end VG.Proof.MillerRabin.Arm
