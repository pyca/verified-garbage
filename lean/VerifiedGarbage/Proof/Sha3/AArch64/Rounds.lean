module

public import VerifiedGarbage.Proof.Sha3.AArch64.Eval
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Round
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Keccak-f[1600] on AArch64: a round's code computes the round

Each round's code, but for ι, run over forms (`Eval.lean`) from the lanes in
their registers leaves, in the registers of the next round, the forms that θ,
ρ, π and χ make of them (`Forms.chiForm`): the kernel evaluates it.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Rounds

open VG VG.AArch64 VG.Proof.Sha3.Forms VG.Proof.Sha3.AArch64.Eval
open VG.Impl.Sha3.AArch64.Lanes (home)

theorem home_lt : ∀ r < 2, ∀ i < 25, home r i < 25 := by decide
theorem home_home : ∀ r < 2, ∀ i < 25, home r (home r i) = i := by decide

/-- The home of lane `i` before round `r`, for any `r`. -/
theorem home_mod (r i : Nat) : home r i = home (r % 2) i := by
  simp only [home, Nat.mod_mod]

/-! ## Vector registers -/

namespace Vec
open VG.Impl.Sha3.AArch64.Sha3.Vector

/-- Doublewords 0 and 1 of the lanes' registers hold the states `A` and `B`, before round `r`. -/
def Pairs (r : Nat) (s : State) (A B : Spec.Sha3.State) : Prop :=
  ∀ i < 25, vdword (s.v (reg r i)) 0 = A[i]! ∧ vdword (s.v (reg r i)) 1 = B[i]!

/-- The lanes in their registers before round `r`. -/
def start (r : Nat) : File := (List.range 32).map fun j => if j < 25 then some (.ofLane (home r j)) else none

/-- The code `is` of round `r` computes the round. -/
def ok (is : List Instr) (r : Nat) : Bool :=
  match evalV is (start r) with
  | some e => (List.range 25).all fun i => vget e (reg (r + 1) i) == some (chiForm (i % 5) (i / 5))
  | none => false

theorem vreg_idx : ∀ r : VReg, vreg r.ctorIdx = r := by intro r; cases r <;> rfl

theorem round_ok {is : List Instr} {r : Nat} (hr : r < 2) (h : ok is r = true) {s : State} {A B : Spec.Sha3.State}
    (hp : Pairs r s A B) : ∃ s', runBlock isa is s = some s' ∧ Pairs (r + 1) s' (core A) (core B) ∧ OnlyV s s' := by
  unfold ok at h
  split at h
  · rename_i e he
    have hrel : RelV (fun q i => if q = 0 then A[i]! else B[i]!) (start r) s := by
      intro v f hf q hq
      simp only [vget, start, List.getD_eq_getElem?_getD, List.getElem?_map] at hf
      rcases hj : (List.range 32)[v.ctorIdx]? with _ | j
      · rw [hj] at hf; simp at hf
      rw [hj] at hf
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
      simp only [List.getElem_range, Option.map_some, Option.getD_some] at hf
      split at hf
      · rename_i h25
        cases hf
        have h1 := home_lt r hr _ h25
        have := hp (home r v.ctorIdx) h1
        simp only [reg, home_home r hr _ h25, vreg_idx] at this
        have hl := Is.lane (env := fun i => if q = 0 then A[i]! else B[i]!) h1
        rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
        · simp only [ite_true, this.1] at hl ⊢; exact hl
        · simp only [Nat.one_ne_zero, ite_false, this.2] at hl ⊢; exact hl
      · cases hf
    obtain ⟨s', x', r', o'⟩ := runV is hrel he
    refine ⟨s', x', fun i hi => ?_, o'⟩
    have hv := beq_iff_eq.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi))
    exact ⟨(r' _ _ hv 0 (by decide)).unique (chi_is A hi), (r' _ _ hv 1 (by decide)).unique (chi_is B hi)⟩
  · cases h

end Vec

/-! ## General registers -/

namespace Gen
open VG.Impl.Sha3.AArch64.Scalar

/-- The lanes' registers hold the state `A`, before round `r`, each pending its rotation. -/
def Lanes (pd : Nat → Nat) (r : Nat) (s : State) (A : Spec.Sha3.State) : Prop :=
  ∀ i < 25, s.gpr (reg r i) = A[i]!.rotateRight (pd i)

/-- The place of a lane's register, if it is one. -/
def place (g : Nat) : Option Nat := (List.range 25).find? fun j => (lreg j).ctorIdx == g

/-- The lanes in their registers before round `r`. -/
def start (pd : Nat → Nat) (r : Nat) : Eval.Env :=
  ⟨(List.range 29).map fun g => (place g).map fun j =>
      (Form.ofLane (home r j)).rot ((64 - pd (home r j)) % 64), List.replicate 4 none⟩

/-- The code `is` of round `r` computes the round, with lanes spilled as `m` says, writing only `w`. -/
def ok (pd : Nat → Nat) (m : Mode) (w : Nat) (is : List Instr) (r : Nat) : Bool :=
  match evalS m w is (start pd r) with
  | some e => (List.range 25).all fun i =>
      gget e (reg (r + 1) i) == some ((chiForm (i % 5) (i / 5)).rot ((64 - pd i) % 64))
  | none => false

theorem pd_lt (c : Conf) : ∀ i < 25, c.pd i < 64 := by
  have : ∀ i < 25, pend i < 64 := by decide
  intro i hi; unfold Conf.pd; split
  · exact this i hi
  · decide

theorem round_ok {pd : Nat → Nat} (hpd : ∀ i < 25, pd i < 64) {m : Mode} {w : Nat} (hb : w.testBit m.b.ctorIdx = false) {is : List Instr} {r : Nat} (hr : r < 2) (h : ok pd m w is r = true) {s : State}
    {A : Spec.Sha3.State} (hm : ModeOk m s) (hp : Lanes pd r s A) :
    ∃ s', runBlock isa is s = some s' ∧ Lanes pd (r + 1) s' (core A) ∧ KeepS m w s s' := by
  unfold ok at h
  split at h
  · rename_i e he
    have hrel : RelS (fun i => A[i]!) m (start pd r) s := by
      refine ⟨fun v f hf => ?_, fun k f _ hf => ?_⟩
      · simp only [gget, start, List.getD_eq_getElem?_getD, List.getElem?_map] at hf
        rcases hj : (List.range 29)[v.ctorIdx]? with _ | j
        · rw [hj] at hf; simp at hf
        rw [hj] at hf
        obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
        simp only [List.getElem_range, Option.map_some, Option.getD_some, Option.map_eq_some_iff] at hf
        obtain ⟨j, hj, rfl⟩ := hf
        have hm := List.mem_range.mp (List.mem_of_find?_eq_some hj)
        have hv : lreg j = v := regIdx_inj (beq_iff_eq.mp (List.find?_some (p := fun j => (lreg j).ctorIdx == v.ctorIdx) hj))
        have h1 := home_lt r hr _ hm
        have := hp (home r j) h1
        simp only [reg, home_home r hr _ hm, hv] at this
        rw [this]
        exact (Is.lane (env := fun i => A[i]!) h1).ror (hpd _ h1)
      · simp only [start, List.getD_eq_getElem?_getD, List.getElem?_replicate] at hf
        split at hf <;> simp at hf
    obtain ⟨s', x', r', k'⟩ := runS hb is hrel hm he
    refine ⟨s', x', fun i hi => ?_, k'⟩
    have hv := beq_iff_eq.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi))
    exact (r'.reg _ _ hv).unique ((chi_is A hi).ror (hpd i hi))
  · cases h

end Gen

end VG.Proof.Sha3.AArch64.Rounds
