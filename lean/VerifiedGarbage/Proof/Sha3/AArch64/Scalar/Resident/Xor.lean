import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Unrolled
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.AbsorbBlock

/-!
# The scalar resident absorber: XORing a block into the lane registers
-/

namespace VG.Proof.Sha3.AArch64.Scalar.Resident

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Resident
open VG.Proof.Sha3.AArch64.Scalar.Boundary
open VG.Proof.Sha3 (laneAddr)

/-- What XORing words into the lanes keeps: every register but `x26` and the
lanes, and all else. -/
structure XorKeep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x26 → (∀ i < 25, r ≠ laneReg i) → s'.gpr r = s.gpr r
  v : s'.v = s.v
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem XorKeep.refl (s : State) : XorKeep s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem XorKeep.trans {s t u : State} (h : XorKeep s t) (k : XorKeep t u) : XorKeep s u :=
  ⟨fun r a b => (k.gpr r a b).trans (h.gpr r a b), k.v.trans h.v, k.mem.trans h.mem,
    k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp⟩

structure LanesInv (s₀ : State) (A : Spec.Sha3.State) (k : Nat) (s : State) : Prop where
  keep : XorKeep s₀ s
  lanes : ∀ j (hj : j < 25), s.gpr (laneReg j) =
    A[j] ^^^ (if j < k then s₀.mem.readW (laneAddr (s₀.gpr .x27) j) 64 else 0)

theorem x27_not_lane : ∀ i < 25, Reg.x27 ≠ laneReg i := by decide
theorem x26_not_lane : ∀ i < 25, Reg.x26 ≠ laneReg i := by decide

theorem absorbLanes_ok (s₀ : State) (A : Spec.Sha3.State) (hA : Boundary.Lanes s₀ A) (n : Nat) (hn : n ≤ 25)
    (hin : ∀ i < n, InRegions (s₀.rd ++ s₀.wr) (laneAddr (s₀.gpr .x27) i) 8) :
    WP isa (.block (absorbLanes n)) s₀ fun s => XorKeep s₀ s ∧
      Boundary.Lanes s (Sha3.Vector.xorWords A s₀.mem (s₀.gpr .x27) n) := by
  refine (wp_range_flatMap (M := isa) (LanesInv s₀ A) (fun i s hi hs => ?_) n (Nat.le_refl _) s₀
    ⟨XorKeep.refl _, fun j hj => ?_⟩).mono fun s hs => ⟨hs.keep, fun j hj => ?_⟩
  · have h27 : s.gpr .x27 = s₀.gpr .x27 := hs.keep.gpr .x27 (by decide) (x27_not_lane)
    refine WP.cons (exec_ldr_x ⟨by omega, by omega⟩ ?_) (WP.cons rfl (wp_nil ?_))
    · rw [hs.keep.rd, hs.keep.wr, h27]; exact hin i hi
    · have hil : i < 25 := by omega
      refine ⟨⟨fun r a b => ?_, hs.keep.v, hs.keep.mem, hs.keep.rd, hs.keep.wr, hs.keep.sp⟩,
        fun j hj => ?_⟩
      · simp only [RegUpd.gpr_write, b i hil, a, ite_false]
        exact hs.keep.gpr r a b
      · simp only [RegUpd.gpr_write, State.read, Size.bits, BitVec.setWidth_eq, h27, hs.keep.mem]
        by_cases he : j = i
        · subst j
          simp only [ite_true, Ne.symm (x26_not_lane i hil), ite_false, hs.lanes i hil,
            show ¬ i < i from Nat.lt_irrefl i, show i < i + 1 from Nat.lt_succ_self i]
          exact congrArg (· ^^^ _) BitVec.xor_zero
        · have hne : laneReg j ≠ laneReg i := fun h => he ((laneReg_inj j hj i hil).mp h)
          simp only [hne, ite_false, (x26_not_lane j hj).symm, hs.lanes j hj]
          congr 1
          by_cases hji : j < i
          · simp only [hji, show j < i + 1 by omega, ite_true]
          · simp only [hji, show ¬ j < i + 1 by omega, ite_false]
  · simp only [Nat.not_lt_zero, ite_false]
    exact (hA j hj).trans BitVec.xor_zero.symm
  · rw [hs.lanes j hj, Sha3.Vector.xorWords_get A _ _ n j hj]

theorem rate_words {r : Nat} (hr : r ∈ Spec.Sha3.rates) : r / 8 ≤ 25 ∧ 8 * (r / 8) = r ∧ r < 4096 := by
  simp only [Spec.Sha3.rates, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-- A whole block of the rate `r`, at `x27`, XORed into the lanes. -/
theorem absorbRate_ok (s : State) (A : Spec.Sha3.State) (hA : Boundary.Lanes s A)
    (r : Nat) (hr : r ∈ Spec.Sha3.rates) (hin : Covers [⟨s.gpr .x27, r⟩] (s.rd ++ s.wr)) :
    WP isa (.block (absorbLanes (r / 8))) s fun s' => XorKeep s s' ∧
      Boundary.Lanes s' (Spec.Sha3.xorBytes A (Spec.Sha3.bytesAt s.mem (s.gpr .x27) r)) := by
  obtain ⟨h25, h8, -⟩ := rate_words hr
  refine (absorbLanes_ok s A hA (r / 8) h25 fun i hi => ?_).mono fun s' h => ⟨h.1, ?_⟩
  · exact hin _ _ ⟨⟨s.gpr .x27, r⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · simpa only [Sha3.Vector.xorWords_eq, h8] using h.2

theorem select_ok (rs : List Nat) (hsmall : ∀ r ∈ rs, r < 4096 ∧ r ∈ Spec.Sha3.rates)
    (s : State) (A : Spec.Sha3.State) (hA : Boundary.Lanes s A)
    (r : Nat) (hr : r ∈ Spec.Sha3.rates) (hrs : r ∈ rs ++ [168])
    (hv : s.gpr .x28 = BitVec.ofNat 64 r)
    (hin : Covers [⟨s.gpr .x27, r⟩] (s.rd ++ s.wr)) :
    WP isa (selectFrom rs) s fun s' => XorKeep s s' ∧
      Boundary.Lanes s' (Spec.Sha3.xorBytes A (Spec.Sha3.bytesAt s.mem (s.gpr .x27) r)) := by
  induction rs generalizing s with
  | nil =>
    have he : r = 168 := by simpa only [List.nil_append, List.mem_singleton] using hrs
    subst r
    exact absorbRate_ok s A hA 168 hr hin
  | cons x xs ih =>
    change WP isa (.seq (.block [.subImm .x .x26 .x28 x]) (.ite (.zero .x .x26) _ _)) s _
    apply WP.seq
    refine WP.cons (exec_subImm_x (hsmall x (by simp)).1) (wp_nil ?_)
    let t := s.write .x .x26 (s.read .x .x28 - BitVec.ofNat 64 x)
    have hk : XorKeep s t := ⟨fun q hq _ => by simp only [t, RegUpd.gpr_write, hq, ite_false],
      rfl, rfl, rfl, rfl, rfl⟩
    have htA : Boundary.Lanes t A := fun i hi => by
      simp only [t, RegUpd.gpr_write, Ne.symm (x26_not_lane i hi), ite_false]
      exact hA i hi
    have h27 : t.gpr .x27 = s.gpr .x27 := hk.gpr .x27 (by decide) x27_not_lane
    have hvt : t.gpr .x28 = BitVec.ofNat 64 r := (hk.gpr .x28 (by decide) (by decide)).trans hv
    have htin : Covers [⟨t.gpr .x27, r⟩] (t.rd ++ t.wr) := by rw [h27]; exact hin
    by_cases he : r = x
    · subst x
      refine WP.ite true ?_ (fun _ => ?_) (fun h => by contradiction)
      · simp only [eval_zero, RegUpd.gpr_write_self, State.read, Size.bits,
          BitVec.setWidth_eq, hv, BitVec.sub_self]
        rfl
      · refine (absorbRate_ok t A htA r hr htin).mono fun u h => ⟨hk.trans h.1, ?_⟩
        rw [← h27]; exact h.2
    · refine WP.ite false ?_ (fun h => by contradiction) (fun _ => ?_)
      · have hn : BitVec.ofNat 64 r - BitVec.ofNat 64 x ≠ 0 := by
          intro h
          have h' : BitVec.ofNat 64 r = BitVec.ofNat 64 x :=
            (BitVec.sub_eq_iff_eq_add.mp h).trans (BitVec.zero_add _)
          have hrb := (rate_words hr).2.2
          have hx := (hsmall x (by simp)).1
          have hh := congrArg BitVec.toNat h'
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : r < 2^64),
            Nat.mod_eq_of_lt (by omega : x < 2^64)] at hh
          exact he hh
        simpa only [eval_zero, t, RegUpd.gpr_write_self, State.read, Size.bits,
          BitVec.setWidth_eq, hv, beq_eq_false_iff_ne] using congrArg some (beq_eq_false_iff_ne.mpr hn)
      · have hrs' : r ∈ xs ++ [168] := by
          simpa only [List.cons_append, List.mem_cons, he, false_or] using hrs
        refine (ih (fun y hy => hsmall y (by simp [hy])) t htA hrs' hvt htin).mono
          fun u h => ⟨hk.trans h.1, ?_⟩
        rw [← h27]; exact h.2

end VG.Proof.Sha3.AArch64.Scalar.Resident
