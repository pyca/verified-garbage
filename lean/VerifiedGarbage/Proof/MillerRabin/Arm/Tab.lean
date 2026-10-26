module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Sq
public import VerifiedGarbage.Proof.MillerRabin.Arm.Scan
import VerifiedGarbage.Proof.Rsa.Arm.RvBase
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The Miller–Rabin round on ARMv7: the table

`tv P σ k` is power `k` in Montgomery form. After `i` steps, entries
0 through `i + 1` are complete, and each remaining entry retains its input
value. Each product is copied once to its final public slot.
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
    if k ≤ i + 1 then tv P σ k else num σ.mem P.B P.W (aT0 + k)

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

/-- A product and one final-slot copy advance the completed prefix. -/
theorem AT_step {P : MP} {σ : State} {i : Nat} (hi : i < 14) :
    ∀ j ∈ LT,
      upd (upd (AT P i σ) aY
        (mm (cOf P σ.mem) P.w (AT P i σ aY) (AT P i σ aX)))
        (aT0 + i + 2) (tv P σ (i + 2)) j = AT P (i + 1) σ j := by
  have ey : mm (cOf P σ.mem) P.w (AT P i σ aY) (AT P i σ aX) = tv P σ (i + 2) := rfl
  rw [ey]
  have e0 : aT0 = 11 := rfl
  have eY : aY = 6 := rfl
  have eX : aX = 5 := rfl
  intro j hj
  have hj' : j = aY ∨ j = aX ∨ (aT0 ≤ j ∧ j < aT0 + 16) := by
    simp only [LT, List.mem_cons, List.not_mem_nil, or_false] at hj
    omega
  rcases hj' with rfl | rfl | hj
  · simp (disch := omega) only [upd, AT, ↓ite_eq_left, ↓ite_eq_right]
  · simp (disch := omega) only [upd, AT, ↓ite_eq_left, ↓ite_eq_right]
  · have hY : j ≠ aY := by omega
    have hX : j ≠ aX := by omega
    by_cases he : j = aT0 + i + 2
    · subst j
      have hsub : aT0 + i + 2 - aT0 = i + 2 := by omega
      simp (disch := omega) only [upd, AT, tabEnt, hsub, ↓ite_eq_left, ↓ite_eq_right]
    · have hidx : j - aT0 ≠ i + 2 := by omega
      have hbound : (j - aT0 ≤ i + 1) = (j - aT0 ≤ (i + 1) + 1) := by apply propext; omega
      simp only [upd, he, hY, hX, AT, tabEnt, ↓reduceIte, hbound]


/-- One fixed, public entry index. -/
theorem tab_step {P : MP} (i : Nat) (hi : i < 14) (fios : Bool := false) :
    VP (TS P (14 - i)) (tabStep i (fios := fios)) (TS P (13 - i)) := by
  let V := fun (_ : State) => upd (fun _ => 0) sK (14 - i)
  refine VP.mono (F := St P (In P) (AT P i) LT V [sK]) ?_
    (fun σ s h => by simpa only [TS, Nat.sub_sub_self (by omega : i ≤ 14)] using h.2)
    (fun _ _ h => h)
  simp only [tabStep, seqs]
  refine VP.seq (St.pmulY (fios := fios) (P := P) (A := AT P i) (L := LT.tail) (.inr rfl)
    (by decide) (by decide) (by decide) (by decide) (fun σ e => tv_lt e _) (fun σ e => e.x5)) ?_
  refine VP.seq (St.pcopy (tabCopy_taint i hi)
    (by simp [wJs, aT0]; omega) (by simp) (by simp only [aT0, aY]; omega)) ?_
  refine (St.pcnt (n := 13 - i) (by simp) (fun σ _ => by simp [V, upd]; omega) (by omega)).mono
    (fun _ _ h => h) fun σ s ⟨h, _⟩ => ?_
  refine ⟨by omega, h.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩)
    (fun d hd => ⟨by simp only [List.mem_singleton] at hd; simp [hd], by
      simp only [List.mem_singleton] at hd; subst d; simp only [upd_self]⟩)⟩
  change upd (upd (AT P i σ) aY _) (aT0 + i + 2) _ j = _
  rw [show (upd (AT P i σ) aY
      (mm (cOf P σ.mem) P.w (AT P i σ aY) (AT P i σ aX))) aY = tv P σ (i + 2) from rfl]
  rw [AT_step hi j hj]
  congr 1
  omega

/-- The fixed entry schedule builds all fourteen remaining powers. -/
theorem tab_build {P : MP} (fios : Bool) (n i : Nat) (hi : i + n = 14) :
    VP (TS P n) (tabBuildFrom fios i n) (TS P 0) := by
  induction n generalizing i with
  | zero => exact VP.block_nil (fun _ _ h => h)
  | succ n ih =>
    simp only [tabBuildFrom]
    have h1 : n + 1 = 14 - i := by omega
    have h2 : n = 13 - i := by omega
    rw [h1]
    exact VP.seq (tab_step i (by omega) (fios := fios)) (by
      rw [← h2]; exact ih (i + 1) (by omega))

theorem tab_loop {P : MP} (fios : Bool := false) :
    VP (TS P 14) (tabBuild (fios := fios)) (TS P 0) := tab_build fios 14 0 rfl

end VG.Proof.MillerRabin.Arm
