module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.VectorBackend
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Lit
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.ToAdditive
public import Aesop.BuiltinRules
public meta import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.VectorBackend
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Resident
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Lit
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Resident
meta import Mathlib.Tactic.NormNum.OfScientific
meta import Mathlib.Tactic.NormNum.DivMod
meta import Mathlib.Tactic.NormNum.Abs
meta import Mathlib.Data.Rat.Cast.Order
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.NormNum.Pow
meta import Mathlib.Tactic.ToAdditive
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
meta import VerifiedGarbage.TCB.Axioms
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Permute
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLoop
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentMath
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ScheduleFacts
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lazy
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.AbsorbBlock
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Permute
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLoop
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentMath
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ScheduleFacts
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lazy
meta import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Spec.Sha3
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.AbsorbBlock
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Sha3.AArch64.Permute

/-! ### `Sha3.AArch64.Scalar.Lazy.Resident`, which only this module used -/

section

/-! ### `Sha3.AArch64.Scalar.Resident.Bulk`, which only this module used -/

section

/-! ### `Sha3.AArch64.Scalar.Resident.Loop`, which this module and modules that import it used -/

section

/-! ### `Sha3.AArch64.Scalar.Resident.Advance`, which this module and modules that import it used -/

section

/-!
# The scalar resident absorber: advancing to the next block
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Resident

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Resident

/-- What advancing changes: `x26`–`x28`, and the data pointer and the length
left in v19 and v20. -/
structure AdvanceKeep (s s' : State) : Prop where
  gpr : ∀ q, q ≠ .x26 → q ≠ .x27 → q ≠ .x28 → s'.gpr q = s.gpr q
  v : ∀ q, q ≠ .v19 → q ≠ .v20 → s'.v q = s.v q
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem advance_ok (s : State) (p : Addr) (n r : Nat) (hr : r ≤ n)
    (hrb : r ≤ 168) (hu : n < 2^63 + r)
    (h19 : vdword (s.v .v19) 0 = p) (h20 : vdword (s.v .v20) 0 = BitVec.ofNat 64 n)
    (h21 : vdword (s.v .v21) 0 = BitVec.ofNat 64 r) :
    WP isa (.block advance) s fun s' => AdvanceKeep s s' ∧
      vdword (s'.v .v19) 0 = p + BitVec.ofNat 64 r ∧
      vdword (s'.v .v20) 0 = BitVec.ofNat 64 (n - r) ∧
      isa.eval (.zero .x .x26) s' = some (decide (r ≤ n - r)) := by
  unfold advance
  refine WP.cons rfl (WP.cons rfl
    (WP.cons (Sha3.Vector.exec_umov_low _ .x27 .v20)
      (WP.cons (Sha3.Vector.exec_umov_low _ .x28 .v21)
        (WP.cons rfl (WP.cons (exec_lsr_x (by decide)) (wp_nil ?_))))))
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 r = BitVec.ofNat 64 (n - r) :=
    VG.Proof.Sha3.sub_ofNat hr
  refine ⟨⟨fun q h26 h27 h28 => ?_, fun q h19 h20 => ?_, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_write, RegUpd.gpr_setV, h26, h27, h28, ite_false]
  · simp only [RegUpd.v_write, RegUpd.v_setV, h19, h20, ite_false]
  · simp only [RegUpd.v_write, RegUpd.v_setV, reduceCtorEq, ite_true, ite_false, VArr.map2, vdword_ofVDwords_0,
      RegUpd.gpr_write, RegUpd.gpr_setV, State.read, Size.bits, BitVec.setWidth_eq, h19, h21]
  · simp only [RegUpd.v_write, RegUpd.v_setV, reduceCtorEq, ite_true, ite_false, VArr.map2, vdword_ofVDwords_0,
      RegUpd.gpr_write, RegUpd.gpr_setV, State.read, Size.bits, BitVec.setWidth_eq, h20, h21, hsub]
  · simp only [eval_zero, RegUpd.gpr_write_self, RegUpd.gpr_write, RegUpd.v_write, RegUpd.v_setV,
      reduceCtorEq, ite_true, ite_false, State.read, Size.bits, BitVec.setWidth_eq,
      VArr.map2, vdword_ofVDwords_0, h20, h21, hsub]
    congr 1
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq, Sha3.Vector.enough_iff (n - r) r (by omega_using [hu]) hrb]
    exact and_iff_left (by omega_using [hu])

end VG.Proof.Sha3.AArch64.Scalar.Resident

end

end

/-! ### `Sha3.AArch64.Scalar.Resident.Xor`, which this module and modules that import it used -/

section

/-!
# The scalar resident absorber: XORing a block into the lane registers
-/

@[expose] public section

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
    refine WP.cons (exec_ldr_x ⟨by omega_using [], by omega_using [hn, hi]⟩ ?_) (WP.cons rfl (wp_nil ?_))
    · rw [hs.keep.rd, hs.keep.wr, h27]; exact hin i hi
    · have hil : i < 25 := by omega_using [hn, hi]
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
          · simp only [hji, show j < i + 1 by omega_using [hji], ite_true]
          · simp only [hji, show ¬ j < i + 1 by omega_using [he, hji], ite_false]
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
  · exact hin _ _ ⟨⟨s.gpr .x27, r⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [h25, hi])⟩
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
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hrb] : r < 2^64),
            Nat.mod_eq_of_lt (by omega_using [hx] : x < 2^64)] at hh
          exact he hh
        simpa only [eval_zero, t, RegUpd.gpr_write_self, State.read, Size.bits,
          BitVec.setWidth_eq, hv, beq_eq_false_iff_ne] using congrArg some (beq_eq_false_iff_ne.mpr hn)
      · have hrs' : r ∈ xs ++ [168] := by
          simpa only [List.cons_append, List.mem_cons, he, false_or] using hrs
        refine (ih (fun y hy => hsmall y (by simp [hy])) t htA hrs' hvt htin).mono
          fun u h => ⟨hk.trans h.1, ?_⟩
        rw [← h27]; exact h.2

end VG.Proof.Sha3.AArch64.Scalar.Resident

end

end

/-!
# The scalar resident absorber: the invariant of its loop

The invariant of the loop over whole blocks (`Loop`): after `c` bytes of
data, the lanes represent the message followed by those bytes, and v19–v21
hold the data pointer, the length left and the rate. The registers it keeps
its values in are not the rounds' temporaries, the boundary's or the
callee-saved ones (`kept_not_temps`, `savedVec_not_kept`,
`preservedV_not_kept`), and the rates are those `select` tests
(`rates_select`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Resident

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Resident
open VG.Proof.Sha3.AArch64.Scalar.Boundary
open VG.Proof.Sha3.AArch64.Sha3.Vector.Resident (BulkPre rate st data len dataR bytesAt_add)
open VG.Spec.Sha3 (stateAt bytesAt)

/-- The loop's invariant, after `c` bytes of data: the lanes are `A`, which
the message followed by those bytes represents, and v19–v21 hold the data
pointer, the length left and the rate. -/
structure Loop (b : State) (c : Nat) (A : Spec.Sha3.State) (s : State) : Prop where
  c_le : c ≤ len b
  aligned : c % rate b = 0
  core : CoreState b A s
  mem : s.mem = b.mem
  dp : vdword (s.v .v19) 0 = data b + BitVec.ofNat 64 c
  left : vdword (s.v .v20) 0 = BitVec.ofNat 64 (len b - c)
  rt : vdword (s.v .v21) 0 = BitVec.ofNat 64 (rate b)
  repr : ∀ msg, stateAt b.mem (st b) = VG.Proof.Sha3.Rep (rate b) msg → msg.length % rate b = 0 →
    A = VG.Proof.Sha3.Rep (rate b) (msg ++ bytesAt b.mem (data b) c)

theorem kept_not_temps : ∀ q ∈ [VReg.v19, .v20, .v21, .v30, .v31],
    q ≠ .v24 ∧ q ≠ .v25 ∧ q ≠ .v28 ∧ q ≠ .v29 := by decide

theorem savedVec_not_kept : ∀ i < 11, Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v19 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v20 := by decide

theorem preservedV_not_kept : ∀ q ∈ preservedV, q ≠ .v19 ∧ q ≠ .v20 := by decide

theorem rates_select {r : Nat} (hr : r ∈ Spec.Sha3.rates) : r ∈ [72, 104, 136, 144] ++ [168] := by
  simp only [Spec.Sha3.rates, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  omega_using [hr]

end VG.Proof.Sha3.AArch64.Scalar.Resident

end

end

/-!
# The scalar resident absorber: before and after its loop

From where the resident absorber of `Sha3.Vector.Resident` runs its bulk
(`BulkPre`), `setup` establishes the loop's invariant (`setup_ok`), and from
it `finish` leaves the state in memory and the arguments as that absorber's
contract for the bulk says (`finish_ok`: `BulkPost`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Resident

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Resident
open VG.Proof.Sha3.AArch64.Scalar.Boundary
open VG.Proof.Sha3.AArch64.Sha3.Vector.Resident (BulkPre BulkPost BulkResult rate st data len
  stateR scratchR)
open VG.Spec.Sha3 (stateAt bytesAt)

theorem setup_ok (b : State) (hp : BulkPre b) :
    WP isa (.block setup) b (Loop b 0 (stateAt b.mem (st b))) := by
  unfold setup
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (save_ok b).mono fun s₁ ⟨hk₁, hg₁, hm₁, hs₁, hp₁, hv₁⟩ => ?_
  unfold keep
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (wp_nil ?_)))
  let s₂ := ((s₁.setV .v19 (ofVDwords (s₁.gpr .x3) (s₁.gpr .x3))).setV .v20
    (ofVDwords (s₁.gpr .x4) (s₁.gpr .x4))).setV .v21 (ofVDwords (s₁.gpr .x6) (s₁.gpr .x6))
  change WP isa (.block Boundary.load) s₂ _
  have hv₂ : ∀ q, q ≠ .v19 → q ≠ .v20 → q ≠ .v21 → s₂.v q = s₁.v q := fun q a c d => by
    simp only [s₂, RegUpd.v_setV, a, c, d, ite_false]
  have hin : ∀ i < 25, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    change InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8
    rw [hk₁.rd, hk₁.wr, hg₁, hp.wr]
    exact ⟨stateR b, by simp, VG.Proof.Sha3.lane_contains _ hi⟩
  refine (load_ok s₂ hin).mono fun s₃ ⟨hk₃, hm₃, hv₃, hl₃⟩ => ?_
  have hst : stateAt s₂.mem (s₂.gpr .x0) = stateAt b.mem (st b) := by
    change stateAt s₁.mem (s₁.gpr .x0) = _
    rw [hm₁, hg₁]
  rw [hst] at hl₃
  have hvb : ∀ q, q ≠ .v19 → q ≠ .v20 → q ≠ .v21 → s₃.v q = s₁.v q := fun q a c d => by
    rw [hv₃]; exact hv₂ q a c d
  have hkv : ∀ q ∈ [VReg.v19, .v20, .v21], ∀ x : Reg, q = .v19 ∧ x = .x3 ∨ q = .v20 ∧ x = .x4 ∨
      q = .v21 ∧ x = .x6 → vdword (s₃.v q) 0 = b.gpr x := by
    intro q _ x hx
    rw [hv₃]
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [s₂, RegUpd.v_setV, reduceCtorEq, ite_true, ite_false, vdword_ofVDwords_0, hg₁]
  refine ⟨Nat.zero_le _, Nat.zero_mod _, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, hl₃⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact hk₃.rd.trans hk₁.rd
  · exact hk₃.wr.trans hk₁.wr
  · exact hk₃.sp.trans hk₁.sp
  · simpa only [Ptrs, hvb .v30 (by decide) (by decide) (by decide),
      hvb .v31 (by decide) (by decide) (by decide)] using hp₁
  · intro i hi
    have hn : ∀ i < 11, Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v19 ∧
        Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v20 ∧
        Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v21 := by decide
    change vdword (s₃.v _) 0 = _
    rw [hvb _ (hn i hi).1 (hn i hi).2.1 (hn i hi).2.2]
    exact hs₁ i hi
  · intro q hq
    have hn : ∀ q ∈ preservedV, q ≠ .v19 ∧ q ≠ .v20 ∧ q ≠ .v21 := by decide
    rw [hvb q (hn q hq).1 (hn q hq).2.1 (hn q hq).2.2]
    exact hv₁ q hq
  · exact hm₃.trans hm₁
  · rw [hkv .v19 (by simp) .x3 (.inl ⟨rfl, rfl⟩), BitVec.add_zero]
  · rw [hkv .v20 (by simp) .x4 (.inr (.inl ⟨rfl, rfl⟩)), Nat.sub_zero, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [hkv .v21 (by simp) .x6 (.inr (.inr ⟨rfl, rfl⟩)), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro msg hm _
    simpa only [bytesAt, List.range_zero, List.map_nil, List.append_nil] using hm

theorem finish_ok (b : State) (hp : BulkPre b) (c : Nat) (A : Spec.Sha3.State) (s : State)
    (h : Loop b c A s) :
    WP isa (.block finish) s (BulkPost b) := by
  unfold finish
  rw [WP.block_append_iff, WP.block_append_iff]
  have hout : ∀ i < 25, InRegions s.wr (b.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [h.core.keep.wr, hp.wr]
    exact ⟨stateR b, by simp, VG.Proof.Sha3.lane_contains _ hi⟩
  refine (store_ok s (b.gpr .x0) A h.core.lanes h.core.ptrs.1 hout).mono
    fun t ⟨hkt, hvt, hft, hat⟩ => ?_
  have hst : SavedVector b t := by simpa only [SavedVector, hvt] using h.core.saved
  refine (restore_ok b t hst).mono fun u ⟨hku, hmu, hvu, hgu⟩ => ?_
  have hv : u.v = s.v := hvu.trans hvt
  refine WP.cons (Sha3.Vector.exec_umov_low _ .x0 .v30) (WP.cons (Sha3.Vector.exec_umov_low _ .x1 .v31)
    (WP.cons (Sha3.Vector.exec_umov_low _ .x3 .v19) (WP.cons (Sha3.Vector.exec_umov_low _ .x4 .v20)
      (WP.cons (Sha3.Vector.exec_umov_low _ .x6 .v21) (WP.cons (exec_addImm_x (by decide))
        (WP.cons rfl (wp_nil ?_)))))))
  refine ⟨c, h.c_le, h.aligned, ⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · have hn : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧
        r ≠ .x6 := by decide
    obtain ⟨n0, n1, n2, n3, n4, n5, n6⟩ := hn r hr
    simp only [RegUpd.gpr_write, n0, n1, n2, n3, n4, n5, n6, ite_false]
    exact hgu r hr
  · exact hku.sp.trans (hkt.sp.trans h.core.keep.sp)
  · simp only [RegUpd.v_write, hv, h.core.vec r hr]
  · exact hku.rd.trans (hkt.rd.trans h.core.keep.rd)
  · exact hku.wr.trans (hkt.wr.trans h.core.keep.wr)
  · simp only [RegUpd.mem_write, hmu]
    rw [← h.mem]
    exact hft.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, Size.bits, BitVec.setWidth_eq,
      RegUpd.v_write, hv]
    exact h.core.ptrs.1
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, Size.bits, BitVec.setWidth_eq,
      RegUpd.v_write, hv]
    exact h.core.ptrs.2
  · simp only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq]
    exact hp.x2.symm
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, Size.bits, BitVec.setWidth_eq,
      RegUpd.v_write, hv]
    exact h.dp
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, Size.bits, BitVec.setWidth_eq,
      RegUpd.v_write, hv]
    exact h.left
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, Size.bits, BitVec.setWidth_eq,
      RegUpd.v_write, hv, State.read, BitVec.add_zero]
    rw [h.core.ptrs.2, hp.x5]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, Size.bits, BitVec.setWidth_eq,
      RegUpd.v_write, hv, h.rt, BitVec.ofNat_toNat]
  · intro msg hm hal
    simp only [RegUpd.mem_write, hmu]
    rw [hat]
    exact h.repr msg hm hal


end VG.Proof.Sha3.AArch64.Scalar.Resident

end

end

/-!
# The scalar resident absorber: the loop over whole blocks

Each iteration XORs a block into the lanes, runs the unrolled rounds of the
permutation (`VG.Proof.Sha3.AArch64.Scalar.Lazy.core_state_keep`) and advances; the lanes then represent
the message followed by one more block (`rep_whole`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Lazy.Resident

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Resident
open VG.Proof.Sha3.AArch64.Scalar.Boundary
open VG.Proof.Sha3.AArch64.Sha3.Vector.Resident (BulkPre rate st data len dataR bytesAt_add)
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.Sha3.AArch64.Scalar.Resident
open VG.Impl.Sha3.AArch64.Scalar.Lazy

theorem body_ok (b : State) (hp : BulkPre b) (c : Nat) (A : Spec.Sha3.State) (s : State)
    (h : Loop b c A s) (hc : c + rate b ≤ len b) :
    WP isa residentBody s fun s' => ∃ A', Loop b (c + rate b) A' s' ∧
      isa.eval (.zero .x .x26) s' = some (decide (rate b ≤ len b - (c + rate b))) := by
  have hrb := Sha3.Vector.Resident.rate_bounds hp
  unfold residentBody xorBlock
  rw [WP.seq_iff, WP.seq_iff]
  refine WP.cons (Sha3.Vector.exec_umov_low s .x27 .v19)
    (WP.cons (Sha3.Vector.exec_umov_low _ .x28 .v21) (wp_nil ?_))
  let s₁ := (s.write .x .x27 (vdword (s.v .v19) 0)).write .x .x28
    (vdword ((s.write .x .x27 (vdword (s.v .v19) 0)).v .v21) 0)
  have h27 : s₁.gpr .x27 = data b + BitVec.ofNat 64 c := by
    simp only [s₁, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, Size.bits,
      BitVec.setWidth_eq, h.dp]
  have h28 : s₁.gpr .x28 = BitVec.ofNat 64 (rate b) := by
    simp only [s₁, RegUpd.gpr_write_self, RegUpd.v_write, Size.bits, BitVec.setWidth_eq, h.rt]
  have hl₁ : Boundary.Lanes s₁ A := fun i hi => by
    simp only [s₁, RegUpd.gpr_write, (scratch_not_lane .x27 (by simp) i hi),
      (scratch_not_lane .x28 (by simp) i hi), ite_false]
    exact h.core.lanes i hi
  have hin : Covers [⟨s₁.gpr .x27, rate b⟩] (s₁.rd ++ s₁.wr) := by
    change Covers [⟨s₁.gpr .x27, rate b⟩] (s.rd ++ s.wr)
    rw [h.core.keep.rd, h.core.keep.wr, h27, hp.rd]
    apply Covers.of_sub
    intro r hr
    have he := List.mem_singleton.mp hr
    subst r
    exact ⟨dataR b, by simp, c, rfl, hc⟩
  refine (select_ok [72, 104, 136, 144] (by decide) s₁ A hl₁ (rate b) hp.rate_mem
    (rates_select hp.rate_mem) h28 hin).mono fun t ⟨hk, hl⟩ => ?_
  rw [h27] at hl
  have hv : t.v = s.v := hk.v
  have hct : CoreState b (Spec.Sha3.xorBytes A (bytesAt s₁.mem (data b + BitVec.ofNat 64 c) (rate b))) t := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, hl⟩
    · exact hk.rd.trans h.core.keep.rd
    · exact hk.wr.trans h.core.keep.wr
    · exact hk.sp.trans h.core.keep.sp
    · simpa only [Ptrs, hv] using h.core.ptrs
    · simpa only [SavedVector, hv] using h.core.saved
    · intro q hq; rw [hv]; exact h.core.vec q hq
  rw [WP.seq_iff]
  refine (VG.Proof.Sha3.AArch64.Scalar.Lazy.core_state_keep b _ t hct).mono fun u ⟨hcu, hku⟩ => ?_
  have hvk : ∀ q ∈ [VReg.v19, .v20, .v21, .v30, .v31], u.v q = s.v q := fun q hq => by
    obtain ⟨a, b', c', d⟩ := kept_not_temps q hq
    rw [hku.v q a b' c' d, hv]
  refine (advance_ok u (data b + BitVec.ofNat 64 c) (len b - c) (rate b) (by omega_using [hc]) (by omega_using [hrb])
    (by have := hp.len_upper; omega_using [this]) ?_ ?_ ?_).mono fun s' ⟨ha, h19, h20, he⟩ => ?_
  · rw [hvk .v19 (by simp)]; exact h.dp
  · rw [hvk .v20 (by simp)]; exact h.left
  · rw [hvk .v21 (by simp)]; exact h.rt
  refine ⟨Spec.Sha3.keccakF (Spec.Sha3.xorBytes A (bytesAt s₁.mem (data b + BitVec.ofNat 64 c) (rate b))),
    ⟨by omega_using [hc], ?_, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Nat.add_mod, h.aligned, Nat.mod_self, Nat.zero_add, Nat.zero_mod]
  · exact ha.rd.trans hcu.keep.rd
  · exact ha.wr.trans hcu.keep.wr
  · exact ha.sp.trans hcu.keep.sp
  · simpa only [Ptrs, ha.v .v30 (by decide) (by decide), ha.v .v31 (by decide) (by decide)] using hcu.ptrs
  · intro i hi
    have hn := savedVec_not_kept i hi
    change vdword (s'.v _) 0 = _
    rw [ha.v _ hn.1 hn.2]
    exact hcu.saved i hi
  · intro q hq
    have hn := preservedV_not_kept q hq
    rw [ha.v q hn.1 hn.2]
    exact hcu.vec q hq
  · intro i hi
    rw [ha.gpr _ (scratch_not_lane .x26 (by simp) i hi) (scratch_not_lane .x27 (by simp) i hi)
      (scratch_not_lane .x28 (by simp) i hi)]
    exact hcu.lanes i hi
  · exact ha.mem.trans (hku.mem.trans (hk.mem.trans h.mem))
  · rw [h19, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [h20, Nat.sub_sub]
  · rw [ha.v .v21 (by decide) (by decide), hvk .v21 (by simp)]; exact h.rt
  · intro msg hmsg halign
    have hm : s₁.mem = b.mem := h.mem
    rw [hm, h.repr msg hmsg halign]
    have hal : (msg ++ bytesAt b.mem (data b) c).length % rate b = 0 := by
      simp only [List.length_append, VG.Proof.Sha3.bytesAt_length, Nat.add_mod, halign,
        h.aligned, Nat.zero_add, Nat.zero_mod]
    rw [← Sha3.Vector.rep_whole hrb.1 (by omega_using [hrb]) _ _ hal (VG.Proof.Sha3.bytesAt_length _ _ _),
      List.append_assoc, ← bytesAt_add]
  · simpa only [Nat.sub_sub] using he

/-- The loop absorbs whole blocks while at least one is left. -/
theorem loop_ok (b : State) (hp : BulkPre b) (A₀ : Spec.Sha3.State) (s₀ : State)
    (h₀ : Loop b 0 A₀ s₀) :
    WP isa (.loop residentBody (.zero .x .x26)) s₀ fun s => ∃ c A, Loop b c A s := by
  let Inv : Nat → State → Prop := fun n s => ∃ c A, Loop b c A s ∧
    n = len b - c ∧ c + rate b ≤ len b
  refine WP.loop (M := isa) Inv (fun n s ⟨c, A, h, hn, hc⟩ => ?_) (len b) s₀ ?_
  · refine (body_ok b hp c A s h hc).mono fun s' ⟨A', h', he⟩ => ?_
    by_cases hk : rate b ≤ len b - (c + rate b)
    · right
      refine ⟨?_, len b - (c + rate b), ?_, c + rate b, A', h', rfl, ?_⟩
      · simpa only [hk, decide_true] using he
      · have := (Sha3.Vector.Resident.rate_bounds hp).1
        omega_using [hn, hc, this]
      · omega_using [hc, hk]
    · left
      exact ⟨by simpa only [hk, decide_false] using he, c + rate b, A', h'⟩
  · exact ⟨0, A₀, h₀, by omega_using [], by simpa only [Nat.zero_add] using hp.enough⟩

theorem functional (b : State) (hp : BulkPre b) :
    WP isa VG.Impl.Sha3.AArch64.Scalar.Lazy.bulk b
      (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.BulkPost b) := by
  unfold VG.Impl.Sha3.AArch64.Scalar.Lazy.bulk
  rw [WP.seq_iff]
  refine (VG.Proof.Sha3.AArch64.Scalar.Resident.setup_ok b hp).mono fun s₀ h₀ => ?_
  rw [WP.seq_iff]
  refine (loop_ok b hp _ s₀ h₀).mono fun s ⟨c, A, h⟩ => ?_
  exact VG.Proof.Sha3.AArch64.Scalar.Resident.finish_ok b hp c A s h

end VG.Proof.Sha3.AArch64.Scalar.Lazy.Resident

end

end

/-!
# The scalar Keccak backend with its resident absorb

The scalar permutation (`VectorSlots`), whose sponge absorbs whole blocks
with the state in registers (`Scalar.Resident.bulk`) under the resident
absorber's guards (`Sha3.Vector.Resident.absorbWith`), falling back to the
ordinary streaming absorb for the rest.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Lazy.ResidentBackend

open VG VG.AArch64

def callee : Impl.Sha3.AArch64.Callee :=
  { VectorSlots.callee with
    absorbOverride := some (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorbWith
      Impl.Sha3.AArch64.Scalar.Lazy.bulk VectorSlots.callee) }

/-! ## Summaries for the constant-time checks

`callee` differs from `VectorSlots.callee` only in its absorb, so the
summaries of the permutation, `pad` and `squeeze` are `VectorSlots.VSums`'s
(what `sponge_taint_summaries VSums callee saving` would prove again), and
only the absorb's are proven here, over them. -/

taint_summary VSums.absorb23 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x23, .x25, .x26, .x27, .x28])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm VectorSlots.VSums.rounds

taint_summary VSums.absorb24 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x24, .x25, .x26, .x27, .x28])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm VectorSlots.VSums.rounds

taint_summary VSums.absorb28 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27, .x28])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm VectorSlots.VSums.rounds

taint_summary VSums.absorb27 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm VectorSlots.VSums.rounds

taint_summary VSums.absorb24_26 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x24, .x25, .x26])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm VectorSlots.VSums.rounds

/-- `sponge_taint_decide VSums`, with the summaries of the absorb above and
`VectorSlots.VSums`'s others, in the same order. -/
tactic_template "sha3_lazy_resident_taint_decide" : tactic => `(tactic|
  taint_decide_sum [
    VSums.absorb23, VSums.absorb24, VSums.absorb28, VSums.absorb27, VSums.absorb24_26,
    VectorSlots.VSums.pad28, VectorSlots.VSums.pad27, VectorSlots.VSums.pad26,
    VectorSlots.VSums.squeeze28, VectorSlots.VSums.squeeze27, VectorSlots.VSums.squeeze26,
    VectorSlots.VSums.perm28s, VectorSlots.VSums.perm27s, VectorSlots.VSums.perm26s,
    VectorSlots.VSums.permS, VectorSlots.VSums.perm28, VectorSlots.VSums.perm27,
    VectorSlots.VSums.perm26, VectorSlots.VSums.perm, VectorSlots.VSums.rounds, MlKemSums.add, MlKemSums.sub,
    MlKemSums.ce, MlKemSums.dd, MlKemSums.ce1024, MlKemSums.dd1024])

/-- The summaries the sponge's callers' checks use (`Callers.sums`). -/
theorem callerSums : Taint.AllOk VectorTaint.taint (Callers.sums callee) :=
  Callers.sums_ok (by
    exact
      .cons (VSums.absorb23.weaken (by decide)) <|
      .cons (VSums.absorb24.weaken (by decide)) <|
      .cons (VSums.absorb28.weaken (by decide)) <|
      .cons (VSums.absorb27.weaken (by decide)) <|
      .cons (VSums.absorb24_26.weaken (by decide)) <|
      .cons (VectorSlots.VSums.pad28.weaken (by decide)) <|
      .cons (VectorSlots.VSums.pad27.weaken (by decide)) <|
      .cons (VectorSlots.VSums.pad26.weaken (by decide)) <|
      .cons (VectorSlots.VSums.squeeze28.weaken (by decide)) <|
      .cons (VectorSlots.VSums.squeeze27.weaken (by decide)) <|
      .cons (VectorSlots.VSums.squeeze26.weaken (by decide)) <|
      .cons (VectorSlots.VSums.perm28s.weaken (by decide)) <|
      .cons (VectorSlots.VSums.perm27s.weaken (by decide)) <|
      .cons (VectorSlots.VSums.perm26s.weaken (by decide)) <|
      .cons (VectorSlots.VSums.permS.weaken (by decide)) <|
      .cons (VectorSlots.VSums.perm28.weaken (by decide)) <|
      .cons (VectorSlots.VSums.perm27.weaken (by decide)) <|
      .cons (VectorSlots.VSums.perm26.weaken (by decide)) <|
      .cons (VectorSlots.VSums.perm.weaken (by decide)) <|
      .nil)

theorem bulk_depth : Impl.Sha3.AArch64.Scalar.Lazy.bulk.aarch64Depth = 0 := by rfl

theorem absorb_correct (a : State) (hp : Proof.Sha3.absorbAArch64.pre a) :
    ∃ t q, Exec isa (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorbWith
      Impl.Sha3.AArch64.Scalar.Lazy.bulk VectorSlots.callee) a t q ∧
      abiPreserved a q ∧ Proof.Sha3.absorbAArch64.post a q :=
  Sha3.Vector.Resident.absorb_correct VectorSlots.backend _ Resident.functional a hp


theorem absorbTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.absorbWith callee) h).isSome = true :=
  by sha3_lazy_resident_taint_decide

theorem padTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x4])
    (Impl.Sha3.AArch64.Stream.padWith callee) h).isSome = true :=
  by exact VectorSlots.padTaint

theorem squeezeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.squeezeWith callee) h).isSome = true :=
  by exact VectorSlots.squeezeTaint

theorem mldsaNttTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 168 1008) h).isSome = true :=
  Callers.mldsaNttTaint _ callerSums

theorem mldsaBallTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 272) h).isSome = true :=
  Callers.mldsaBallTaint _ callerSums

theorem mldsaMaskTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.expandMaskTailWith callee) h).isSome = true :=
  Callers.mldsaMaskTaint _ callerSums

theorem mldsaSeedsTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x25, 0, 32⟩, ⟨.x28, 896, 2⟩] [⟨.x28, 1024, 128⟩]) h).isSome = true :=
  Callers.mldsaSeedsTaint _ callerSums

theorem mldsaTrHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.trHashWith callee p) h).isSome = true :=
  Callers.mldsaTrHashTaint _ callerSums

theorem mldsaVerifyHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x26, 0, 64⟩,
      ⟨.x28, (Impl.MlDsa.AArch64.Verify.bP p).2, p.k * Impl.MlDsa.AArch64.Verify.w1Len p⟩]
      [⟨.x28, 1024, p.ctildeLen⟩]) h).isSome = true :=
  Callers.mldsaVerifyHashTaint _ callerSums

theorem mldsaSignDecodeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, 960, 64⟩) h).isSome = true :=
  Callers.mldsaSignDecodeTaint _ callerSums

theorem mldsaSignCommitTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x26, 0, 64⟩,
      ⟨.x28, 2048, p.k * Impl.MlDsa.AArch64.Sign.w1Len p⟩]
      ⟨.x28, 1040, Impl.MlDsa.AArch64.Sign.cLen p⟩) h).isSome = true :=
  Callers.mldsaSignCommitTaint _ callerSums

def backend : Permutation where
  callee := callee
  features := []
  ok := VG.Proof.Sha3.AArch64.Scalar.Lazy.permute_correct
  noFrames := VG.Proof.Sha3.AArch64.Scalar.Lazy.permute_noFrames
  noDit := by lit_decide
  callerSums := callerSums
  absorbOverrideOk := by
    intro code h
    cases h
    exact absorb_correct
  absorbOverrideNoDit := by intro code h; cases h; lit_decide
  absorbOverrideDepth := by
    intro code h
    cases h
    exact Sha3.Vector.Resident.absorb_depth VectorSlots.backend _ bulk_depth
  absorbTaint := absorbTaint
  padTaint := padTaint
  squeezeTaint := squeezeTaint
  mldsaNttTaint := mldsaNttTaint
  mldsaBallTaint := mldsaBallTaint
  mldsaMaskTaint := mldsaMaskTaint

  mldsaSeedsTaint := mldsaSeedsTaint
  mldsaTrHashTaint := mldsaTrHashTaint
  mldsaVerifyHashTaint := mldsaVerifyHashTaint

  mldsaSignDecodeTaint := mldsaSignDecodeTaint
  mldsaSignCommitTaint := mldsaSignCommitTaint

end VG.Proof.Sha3.AArch64.Scalar.Lazy.ResidentBackend
