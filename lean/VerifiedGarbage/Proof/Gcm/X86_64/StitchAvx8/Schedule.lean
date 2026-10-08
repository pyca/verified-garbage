import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Stages
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Aes
import Mathlib.Tactic.IntervalCases

/-! # Connecting the hash and counter work to the fixed AES schedules -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs q8 prepCounter gh8 prepare reduceFinal)
open VG.Spec.Gcm (Block)

/-- Number of hash inputs consumed before round `j`. -/
def hashCount (nr j : Nat) : Nat :=
  ((if nr = 10 then [1, 2, 3, 4, 5, 6, 7, 8]
    else if nr = 12 then [1, 2, 3, 5, 6, 7, 9, 10]
    else [1, 2, 4, 6, 8, 10, 11, 12]).filter (fun k => k < j)).length

/-- Counter preparation is split over the first two AES rounds. -/
def counterCount (j : Nat) : Nat := if j ≤ 1 then 0 else if j = 2 then 4 else 8

def workRegs : List XReg := .xmm1 :: .xmm2 :: ghRegs

/-- The three schedules have the same abstract steps: eight products,
then one reduction, with idle slots in the longer AES schedules. -/
theorem schedule_cases : ∀ nr < 15, nr = 10 ∨ nr = 12 ∨ nr = 14 → ∀ j < 15,
    1 ≤ j → j < nr → ∀ more : Bool,
    (hashCount nr j < 8 ∧ hashCount nr (j + 1) = hashCount nr j + 1 ∧
      j + 1 < nr ∧ q8 nr more j = gh8 ((hashCount nr j + 1) % 8) ++
        (if more then prepare (8 + (hashCount nr j + 1) % 8) else [])) ∨
    (hashCount nr j = 8 ∧ hashCount nr (j + 1) = 8 ∧ j + 1 = nr ∧
      q8 nr more j = reduceFinal) ∨
    (hashCount nr (j + 1) = hashCount nr j ∧ j + 1 < nr ∧ q8 nr more j = []) := by
  intro nr _ hn j _ hj hjn more
  rcases hn with rfl | rfl | rfl <;> interval_cases j <;> simp [hashCount, q8]

theorem q8_ok {s₀ start s : State} {P X Y : Nat → Block} {y : Block}
    {c nc : Nat} (hp : SPre s₀) (j : Nat) (hj : 1 ≤ j) (hjn : j < nr s₀)
    (h : StageInv s₀ start P X Y y c nc (hashCount (nr s₀) j) false s)
    (more : Bool)
    (hr : more = true → ∀ k < 16, InRegions (s₀.rd ++ s₀.wr)
      (start.gpr .rdx + BitVec.ofNat 64 (16 * k)) 16)
    (hs : more = true → ∀ k < 16, Region.Disjoint
      ⟨start.gpr .rdx + BitVec.ofNat 64 (16 * k), 16⟩ (pR s₀))
    (hx : more = true → ∀ k < 16, Spec.Gcm.blockAt start.mem
      (start.gpr .rdx + BitVec.ofNat 64 (16 * k)) = X k)
    (hY : ∀ i < 8, Y i = if more then X (8 + i) else X i) :
    WP isa (.block (q8 (nr s₀) more j)) s fun t =>
      StageInv s₀ start P X Y y c nc (hashCount (nr s₀) (j + 1))
        (decide (nr s₀ ≤ j + 1)) t ∧ FlowFrame workRegs s t := by
  have hn : nr s₀ < 15 := by rcases hp.rounds with h | h | h <;> omega
  rcases schedule_cases _ hn hp.rounds j (by omega) hj hjn more with
    ⟨h8, hnext, hlt, hc⟩ | ⟨h8, hnext, he, hc⟩ | ⟨hnext, hlt, hc⟩
  · rw [hc, hnext, show decide (nr s₀ ≤ j + 1) = false from decide_eq_false (by omega)]
    exact WP.mono (h.hashStep hp h8 more hr hs hx hY) fun t ⟨ht, hf⟩ =>
      ⟨ht, hf.mono (by decide)⟩
  · rw [hc, hnext, he, show decide (nr s₀ ≤ nr s₀) = true from decide_eq_true (Nat.le_refl _)]
    rw [h8] at h
    exact h.finishHash hp
  · rw [hc, hnext, show decide (nr s₀ ≤ j + 1) = false from decide_eq_false (by omega)]
    exact WP.block_nil ⟨h, .refl _ _⟩
 
/-- The counter work appended to the hash work in each AES round. -/
def counterWork (j : Nat) : List Instr :=
  if 1 ≤ j ∧ j ≤ 2 then
    (List.range 4).flatMap (fun i => prepCounter (4 * (j - 1) + i)) else []

theorem counters_ok {s₀ start s : State} {P X Y : Nat → Block} {y : Block}
    {c nh : Nat} {finished : Bool} (hp : SPre s₀) (j : Nat) (hj : 1 ≤ j)
    (h : StageInv s₀ start P X Y y c (counterCount j) nh finished s)
    (hv : (start.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8)) :
    WP isa (.block (counterWork j)) s fun t =>
      StageInv s₀ start P X Y y c (counterCount (j + 1)) nh finished t ∧
        FlowFrame workRegs s t := by
  by_cases h1 : j = 1
  · subst j
    exact WP.mono (h.counters hp 4 (by decide) hv) fun t ⟨ht, hf⟩ =>
      ⟨ht, hf.mono (by decide)⟩
  by_cases h2 : j = 2
  · subst j
    exact WP.mono (h.counters hp 4 (by decide) hv) fun t ⟨ht, hf⟩ =>
      ⟨ht, hf.mono (by decide)⟩
  · have hgt : 2 < j := by omega
    simp only [counterWork, show ¬(1 ≤ j ∧ j ≤ 2) from by omega, ite_false]
    have he : counterCount (j + 1) = counterCount j := by
      simp only [counterCount, show ¬j ≤ 1 from by omega,
        show ¬j + 1 ≤ 1 from by omega, show j + 1 ≠ 2 from by omega, h2, ite_false]
    rw [he]
    exact WP.block_nil ⟨h, .refl _ _⟩

end VG.Proof.Gcm.X86_64.StitchAvx8
