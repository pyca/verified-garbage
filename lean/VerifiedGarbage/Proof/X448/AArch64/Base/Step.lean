import VerifiedGarbage.Proof.X448.AArch64.Base.Negate
import VerifiedGarbage.Proof.X448.AArch64.Base.AddEnv

/-!
# X448 of the base point on AArch64: the comb's invariant

Untrusted: everything here is checked by Lean. The state of the comb before
step `j` (`StepInv`, as Ed25519's `CombInv`), what every phase after the setup
keeps (`Frame`), and the facts about a step's selection and its sums that the
step's proof (`Proof/Ed448/AArch64/Point56/Comb.lean`, whose step calls
`vg_ed448_r56_comb_add`) uses.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env opSwap)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (nib mag)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The entries' slots. -/
def entrySlots : List Index := [6, 7, 8, 9]

theorem slot_entry (i : Index) : i ∈ entrySlots ↔ OX ≤ slot i.val ∧ slot i.val < OX + 512 := by
  have := i.isLt
  simp only [entrySlots, List.mem_cons, List.not_mem_nil, or_false, OX, slot, Fin.ext_iff]
  omega

/-- A selection, in the slot environment. -/
theorem selected_env {s t : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {j ao ae : Nat}
    (h : Selected base j ao ae s t) :
    BEnv t.mem base ∧ Same base entrySlots s.mem t.mem ∧
    EV t.mem base 6 = (Impl.X448.baseTable j ao).1 ∧ EV t.mem base 7 = (Impl.X448.baseTable j ao).2 ∧
    EV t.mem base 8 = (Impl.X448.baseTable j ae).1 ∧ EV t.mem base 9 = (Impl.X448.baseTable j ae).2 ∧
    (∀ i ∈ entrySlots, Bnd Mb t.mem base (slot i.val)) := by
  obtain ⟨hv, hf, _⟩ := h
  have hn := hs.nowrap
  -- Words outside the entries' slots are kept.
  have keep : ∀ i : Index, i ∉ entrySlots → ∀ w < 8, limbs t.mem base (slot i.val) w = limbs s.mem base (slot i.val) w :=
    fun i hi w hw => by
      have := i.isLt
      have hi' := (slot_entry i).not.mp hi
      simp only [OX, slot] at hi'
      exact congrArg BitVec.toNat (hf.word (by simp only [OX, slot]; omega) (by simp only [slot]; omega))
  -- The entries' limbs.
  have lv : ∀ (v : Spec.X448.Fe) (o : Nat), (∀ w < 8, word t.mem base (o + 8 * w) = limb v w) →
      (∀ w < 8, limbs t.mem base o w = (limb v w).toNat) := fun v o h w hw => by
    show (word t.mem base (o + 8 * w)).toNat = _; rw [h w hw]
  have l6 := lv _ OX fun w hw => (hv w hw).1
  have l8 := lv _ EX fun w hw => (hv w hw).2.1
  have l7 := lv _ OY fun w hw => (hv w hw).2.2.1
  have l9 := lv _ EY fun w hw => (hv w hw).2.2.2
  have fe : ∀ (v : Spec.X448.Fe) (o : Nat), (∀ w < 8, limbs t.mem base o w = (limb v w).toNat) →
      VG.Proof.X448.AArch64.Weak.F t.mem base o = v := fun v o h => by
    simp only [VG.Proof.X448.AArch64.Weak.F]
    rw [VG.Proof.X448.Wide.valN_congr h, limb_val, VG.Proof.X448.toFe_self]
  have bd : ∀ (v : Spec.X448.Fe) (o : Nat), (∀ w < 8, limbs t.mem base o w = (limb v w).toNat) →
      Bnd Mb t.mem base o := fun v o h w hw => by
    rw [h w hw]; exact Nat.lt_of_lt_of_le (limb_lt v w) (by decide)
  refine ⟨fun i => ?_, keep, fe _ _ l6, fe _ _ l7, fe _ _ l8, fe _ _ l9, ?_⟩
  · by_cases hi : i ∈ entrySlots
    · simp only [entrySlots, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l6 w hw) (by decide)
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l7 w hw) (by decide)
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l8 w hw) (by decide)
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l9 w hw) (by decide)
    · intro w hw; rw [keep i hi w hw]; exact hb i w hw
  · intro i hi
    simp only [entrySlots, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact bd _ _ l6
    · exact bd _ _ l7
    · exact bd _ _ l8
    · exact bd _ _ l9

/-! ## The invariant -/

open VG.Proof.Ed448 (Rep baseAff dZ)
open VG.Proof.X448 (oddSumZ evenSumZ combG)

/-- The state of a comb of `n` tables before step `j` (of the scalar `k`), from the function's
state after its setup `s₀`. -/
structure StepInv (n : Nat) (s₀ : State) (base : Addr) (k j : Nat) (s : State) : Prop where
  bound : j ≤ n
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  bits : Bits n base k s.mem
  odd : Rep (pt (EV s.mem base) 0 1 2) (((combG n : ℤ) + oddSumZ k j) • baseAff)
  even : Rep (pt (EV s.mem base) 3 4 5) (((combG n : ℤ) + evenSumZ k j) • baseAff)
  lr : s.gpr .x30 = s₀.gpr .x30
  out : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside2 base 64 2816 ACC 1152 s₀.mem s.mem
  tbl : TblAt s base (s₀.syms combSym)

/-- What every phase after the setup keeps. -/
structure Frame (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  lr : s.gpr .x30 = s₀.gpr .x30
  out : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside2 base 64 2816 ACC 1152 s₀.mem s.mem

theorem StepInv.frame {n : Nat} {s₀ s : State} {base : Addr} {k j : Nat} (h : StepInv n s₀ base k j s) :
    Frame s₀ base s := ⟨h.scr, h.env, h.zero, h.lr, h.out, h.rd, h.wr, h.mem⟩

/-! ## A step's pieces -/

open VG.Proof.X448 (addPt addPt_rep basePt negAff baseEntry_ok nib_lt mag_lt sdig)

/-- The selected scalar slots outside `entrySlots` are kept by a selection. -/
theorem Selected.outside2 {base : Addr} {j ao ae : Nat} {s t : State} (h : Selected base j ao ae s t) :
    Outside2 base 64 2816 ACC 1152 s.mem t.mem := fun x h1 _ =>
  h.2.1 x (by simp only [OX, slot] at h1 ⊢; omega)

/-- The entry for the digit `n - 8`, negated as `negate` does. -/
theorem entry_eq (e : Spec.X448.Fe × Spec.X448.Fe) (z : Spec.X448.Fe) (hz : z = 0) (n : Nat) :
    (⟨if decide (n < 8) then z - e.1 else e.1, e.2, 1⟩ : Spec.Ed448.Point) =
      basePt (if n < 8 then negAff e else e) := by
  subst hz
  by_cases hn : n < 8
  · simp only [hn, decide_true, ↓reduceIte]; rfl
  · simp only [hn, decide_false, ↓reduceIte, Bool.false_eq_true]; rfl

theorem acc_step (G : ℤ) (S : ℤ) (n j : Nat) :
    (G + S) • baseAff + (((n : ℤ) - 8) * 256 ^ j) • baseAff = (G + (S + ((n : ℤ) - 8) * 256 ^ j)) • baseAff := by
  rw [← add_smul, add_assoc]

/-- The tables survive what keeps the regions and changes only the scalar slots and `ACC`. -/
theorem TblAt.of_outside2 {s t : State} {base T : Addr} (h : TblAt s base T)
    (hrw : t.rd ++ t.wr = s.rd ++ s.wr) (hm : Outside2 base 64 2816 ACC 1152 s.mem t.mem) :
    TblAt t base T :=
  h.of_far hrw fun x hx => hm x (by omega) (by simp only [ACC]; omega)

end VG.Proof.X448.AArch64.Base
