module

public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.MulCall
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Chain
public import VerifiedGarbage.Proof.Framework.AArch64.StoreFrame
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block

/-!
# Curve448's field product on AArch64: calls on the slots

Untrusted: everything here is checked by Lean. `mulCallE`: a call of `vg_gf448_r56_mul` on
slots of the working space does what the inlined product does to them (`fmulE`): it updates
the result's slot with the product (`opMul`), keeps every slot's limbs below `Ib` and the
result's below `Mb`, and writes nothing but the result and the operand sums.

`PSpec`: what a chain of field operations whose products are calls (the square root's power,
`root`) computes, with the bytes it keeps (outside slots 14–21 and the products' coefficients),
from the inlined operations' `ISpec` and their stores (`PSpec.of_ispec`) and from the calls
(`mulCallP`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps Outside2 limbs FieldMem ofs)
open VG.Proof.X448.AArch64.Weak (Index Env opMul FieldOp applyOps)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same fclob ISpec IKeep FKeep fieldMem_same env_update slot_64
  slot_sep64)
open VG.Proof.Curve448.AArch64.Fast (prodOut clob)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- **A call of `vg_gf448_r56_mul`** on slots, as the inlined product (`fmulE`). -/
theorem mulCallE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o a b : Index)
    (hob : o ≠ b) :
    WP isa (Point56.mulCall (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      Keeps (.x19 :: .x30 :: fclob) s t ∧ t.sp = s.sp ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧
      Outside2 base (slot o.val) 64 ACC 64 s.mem t.mem ∧ BEnv t.mem base ∧
      Bnd Mb t.mem base (slot o.val) ∧ Same base [o] s.mem t.mem ∧
      EV t.mem base = opMul o a b (EV s.mem base) := by
  have hA : ACC = 3584 := rfl
  refine WP.mono (mulCall_ok hs (slot_64 o) (slot_64 a) (slot_64 b) (slot_sep64 hob) (hb a) (hb b))
    fun t ⟨tv, tm, tk, tsp, tV⟩ => ?_
  have fm : FieldMem base (slot o.val) s.mem t.mem := fun x h1 h2 =>
    tm x (by omega) (by have : VG.Impl.Curve448.AArch64.Fast.KA = 3584 := rfl; omega)
  have bo : Bnd Mb t.mem base (slot o.val) := fun i hi => by
    rw [tv i hi]; exact VG.Proof.Curve448.AArch64.Fast.prod_bound (hb a) (hb b) i hi
  refine ⟨tk, tsp, tV, tm, env_update hb fm (fun i hi =>
    Nat.lt_of_lt_of_le (bo i hi) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib), bo, fieldMem_same fm, ?_⟩
  rw [VG.Proof.X448.AArch64.Weak.E_update fm]
  simp only [opMul]
  refine congrArg (Function.update _ o) ?_
  change VG.Proof.X448.toFe _ = VG.Proof.X448.toFe _ * VG.Proof.X448.toFe _
  rw [VG.Proof.X448.Wide.valN_congr tv]
  exact VG.Proof.Curve448.AArch64.Fast.prod_val _ _

/-! ## Calls keeping `x19` and the return address -/

/-- No instruction of a call writes `v26`. -/
theorem mulCall_noV26' (o a b : Nat) : (Point56.mulCall o a b).allInstrs (fun i => vdstOf i != some .v26) = true := by
  simp only [Point56.mulCall, Code.allInstrs]
  rfl

theorem mulCall_noV26 (o a b : Nat) : ∀ i ∈ instrs (Point56.mulCall o a b), vdstOf i ≠ some .v26 :=
  fun i hi => by
    have h := mulCall_noV26' o a b
    rw [Code.allInstrs_eq] at h
    simpa using List.all_eq_true.mp h i hi

theorem mulCallK_keepsV (o a b : Nat) : (Point56.mulCallK o a b).allInstrs keepsV = true := by
  simp only [Point56.mulCallK, Point56.mulCall, Code.allInstrs]
  rfl

/-- **A call of `vg_gf448_r56_mul` keeping `x19` and `x30`**, as the inlined product: every
register but the product's kept. -/
theorem mulCallK_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : o + 64 ≤ ACC) (ha : a + 64 ≤ ACC) (hb : b + 64 ≤ ACC) (hob : o + 64 ≤ b ∨ b + 64 ≤ o)
    (fa : ∀ i < 8, limbs s.mem base a i < Ib) (fb : ∀ i < 8, limbs s.mem base b i < Ib) :
    WP isa (Point56.mulCallK o a b) s fun t =>
      (∀ i < 8, limbs t.mem base o i = prodOut (limbs s.mem base a) (limbs s.mem base b) i) ∧
      Outside2 base o 64 VG.Impl.Curve448.AArch64.Fast.KA 64 s.mem t.mem ∧ Keeps clob s t ∧
      t.sp = s.sp ∧ (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) := by
  have h : WP isa (Point56.mulCallK o a b) s fun t =>
      (∀ i < 8, limbs t.mem base o i = prodOut (limbs s.mem base a) (limbs s.mem base b) i) ∧
      Outside2 base o 64 VG.Impl.Curve448.AArch64.Fast.KA 64 s.mem t.mem ∧ Keeps clob s t ∧
      t.sp = s.sp := by
    unfold Point56.mulCallK
    rw [WP.seq_iff]
    refine WP.mono (insOf_ok [(.x19, .v26, 0), (.x30, .v26, 1)] s (by decide) (by decide))
      fun s₁ ⟨g₁, m₁, r₁, w₁, sp₁, l₁, _⟩ => ?_
    have hs₁ : Scr s₁ base := hs.of_keeps (rs := []) ⟨fun r _ => by rw [g₁], r₁, w₁⟩ (by decide)
    rw [WP.seq_iff]
    obtain ⟨tr, t, he, tl, tm, tk, tsp, _⟩ := mulCall_ok hs₁ ho ha hb hob (m₁ ▸ fa) (m₁ ▸ fb)
    refine ⟨tr, t, he, ?_⟩
    have hv : t.v .v26 = s₁.v .v26 := Exec.vec (mulCall_noV26 o a b) he
    have l19 : laneOf t .v26 0 = s.gpr .x19 := by
      rw [laneOf, hv, ← laneOf, l₁ (.x19, .v26, 0) List.mem_cons_self]
    have l30 : laneOf t .v26 1 = s.gpr .x30 := by
      rw [laneOf, hv, ← laneOf, l₁ (.x30, .v26, 1) (List.mem_cons_of_mem _ List.mem_cons_self)]
    refine WP.mono (umovOf_ok [(.x19, .v26, 0), (.x30, .v26, 1)] t (by decide) (by decide))
      fun u ⟨um, ur, uw, usp, ul, uo⟩ => ?_
    refine ⟨fun i hi => by rw [um, tl i hi, m₁], by rw [um, ← m₁]; exact tm,
      ⟨fun r hr => ?_, by rw [ur, tk.2.1, r₁], by rw [uw, tk.2.2, w₁]⟩, by rw [usp, tsp, sp₁]⟩
    by_cases h19 : r = .x19
    · subst h19; rw [ul (.x19, .v26, 0) List.mem_cons_self, l19]
    by_cases h30 : r = .x30
    · subst h30; rw [ul (.x30, .v26, 1) (List.mem_cons_of_mem _ List.mem_cons_self), l30]
    rw [uo r (by simp [h19, h30]), tk.1 r (by simp [h19, h30, hr]), g₁]
  exact WP.mono (WP.preservedV h (mulCallK_keepsV o a b)) fun t ⟨⟨h1, h2, h3, h4⟩, h5⟩ =>
    ⟨h1, h2, h3, h4, h5⟩

/-- **A call of `vg_gf448_r56_mul` keeping `x19` and `x30`** on slots, as the inlined product
(`fmulE`). -/
theorem mulCallKE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o a b : Index)
    (hob : o ≠ b) :
    WP isa (Point56.mulCallK (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Bnd Mb t.mem base (slot o.val) ∧
      Same base [o] s.mem t.mem ∧ EV t.mem base = VG.Proof.X448.AArch64.opMul o a b (EV s.mem base) := by
  have hA : ACC = 3584 := rfl
  refine WP.mono (mulCallK_ok hs (slot_64 o) (slot_64 a) (slot_64 b) (slot_sep64 hob) (hb a) (hb b))
    fun t ⟨tv, tm, tk, _, _⟩ => ?_
  have fm : FieldMem base (slot o.val) s.mem t.mem := fun x h1 h2 =>
    tm x (by omega) (by have : VG.Impl.Curve448.AArch64.Fast.KA = 3584 := rfl; omega)
  have bo : Bnd Mb t.mem base (slot o.val) := fun i hi => by
    rw [tv i hi]; exact VG.Proof.Curve448.AArch64.Fast.prod_bound (hb a) (hb b) i hi
  refine ⟨⟨tk, VG.Proof.X448.AArch64.Fast.fieldMem_outside2 fm⟩, env_update hb fm (fun i hi =>
    Nat.lt_of_lt_of_le (bo i hi) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib), bo, fieldMem_same fm, ?_⟩
  rw [VG.Proof.X448.AArch64.Weak.E_update fm]
  simp only [VG.Proof.X448.AArch64.opMul]
  refine congrArg (Function.update _ o) ?_
  change VG.Proof.X448.toFe _ = VG.Proof.X448.toFe _ * VG.Proof.X448.toFe _
  rw [VG.Proof.X448.Wide.valN_congr tv]
  exact VG.Proof.Curve448.AArch64.Fast.prod_val _ _

/-- The call in a chain of the register-resident arithmetic (`ISpec`), as the inlined product. -/
theorem mulCallKI (base : Addr) (o a b : Index) (hob : o ≠ b) :
    ISpec base (Point56.mulCallK (slot o.val) (slot a.val) (slot b.val)) (applyOps [.mul o a b]) :=
  fun _ hs hb => WP.mono (mulCallKE hs hb o a b hob) fun _ ⟨tk, tb, _, _, te⟩ =>
    ⟨tk.ikeep, tb, te⟩

/-! ## Operations with calls -/

open VG.Impl.X448.AArch64.Fast (opsK)

/-- A product in `opsK`: a square inlined, a product of distinct operands a call, either as the
inlined product (`mulOp`). -/
theorem mulOpK {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o a b : Index)
    (hob : a = b ∨ o ≠ b)
    {rest : List Impl.X448.AArch64.Fast.Op} {Q : State → Prop}
    (h : ∀ t, FKeep base s t → BEnv t.mem base → Bnd Mb t.mem base (slot o.val) →
      Same base [o] s.mem t.mem →
      EV t.mem base = Function.update (EV s.mem base) o (EV s.mem base a * EV s.mem base b) →
      WP isa (opsK rest) t Q) :
    WP isa (opsK (.mul (slot o.val) (slot a.val) (slot b.val) :: rest)) s Q := by
  simp only [opsK, Impl.X448.AArch64.Fast.Op.progK]
  split
  · refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Fast.fmulE hs hb o a b hob)
      fun t ⟨tk, tb, tm, ts, te⟩ => h t tk tb tm ts ?_)
    rw [te]; rfl
  · rename_i hab
    have hob' : o ≠ b := hob.resolve_left fun e => hab (e ▸ rfl)
    exact WP.seq (WP.mono (mulCallKE hs hb o a b hob') fun t ⟨tk, tb, tm, ts, te⟩ => h t tk tb tm ts te)

/-- A difference in `opsK`, as in `ops` (`subOp`). -/
theorem subOpK {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {o a b : Index}
    (ha : Bnd Mb s.mem base (slot a.val)) (hb' : Bnd Mb s.mem base (slot b.val)) (hoa : o ≠ a)
    (hob : o ≠ b) {rest : List Impl.X448.AArch64.Fast.Op} {Q : State → Prop}
    (h : ∀ t, FKeep base s t → BEnv t.mem base → Same base [o] s.mem t.mem →
      EV t.mem base = Function.update (EV s.mem base) o (EV s.mem base a - EV s.mem base b) →
      WP isa (opsK rest) t Q) :
    WP isa (opsK (.sub (slot o.val) (slot a.val) (slot b.val) :: rest)) s Q :=
  WP.seq (WP.mono (VG.Proof.X448.AArch64.Fast.subE hs hb ha hb' hoa hob) fun t ⟨tk, tb, ts, te⟩ =>
    h t tk tb ts te)

/-- A copy in `opsK`, as in `ops`. -/
theorem copyOpK {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o a : Index)
    {rest : List Impl.X448.AArch64.Fast.Op} {Q : State → Prop}
    (h : ∀ t, FKeep base s t → BEnv t.mem base → Same base [o] s.mem t.mem →
      EV t.mem base = VG.Proof.X448.AArch64.opCopy o a (EV s.mem base) → WP isa (opsK rest) t Q) :
    WP isa (opsK (.copy (slot o.val) (slot a.val) :: rest)) s Q :=
  WP.seq (WP.mono (VG.Proof.X448.AArch64.Fast.copyE hs hb o a) fun t ⟨tk, tb, _, ts, te⟩ =>
    h t tk tb ts te)

/-! ## Chains with calls -/

/-- The registers a chain with calls may change: the field operations', the counter `x19` (which
the calls change too), and the calls' `x30`. -/
abbrev pclob : List Reg := .x30 :: .x19 :: fclob

/-- What a chain with calls computes: `f` of the slots, every slot's limbs below `Ib`, and every
byte outside slots 14–21 and the products' coefficients kept. -/
def PSpec (base : Addr) (code : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Scr s base → BEnv s.mem base → WP isa code s fun t =>
    Keeps pclob s t ∧ BEnv t.mem base ∧ EV t.mem base = f (EV s.mem base) ∧
      Outside2 base 1856 1024 ACC 1152 s.mem t.mem

theorem PSpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : Env → Env}
    (h₁ : PSpec base c₁ f) (h₂ : PSpec base c₂ g) :
    PSpec base (.seq c₁ c₂) (fun e => g (f e)) := fun s hs hb =>
  WP.seq (WP.mono (h₁ s hs hb) fun t ⟨tk, tb, te, tm⟩ =>
    WP.mono (h₂ t (hs.of_keeps tk (by decide)) tb) fun u ⟨uk, ub, ue, um⟩ =>
      ⟨tk.trans uk, ub, by rw [ue, te], tm.trans um⟩)

/-- Where the inlined operations of the power store: slots 14–21 and the products'
coefficients. -/
def rootOk (d : Nat) : Bool := (1856 ≤ d && d + 8 ≤ 2880) || (3584 ≤ d && d + 8 ≤ 4736)

/-- The bytes outside slots 14–21 and the products' coefficients, from the stores. -/
theorem outside2_of_rootOk {base : Addr} {m m' : Mem}
    (h : ∀ a, Unstored rootOk base a → m' a = m a) : Outside2 base 1856 1024 ACC 1152 m m' := by
  intro a h1 h2
  refine h a fun d hd => ?_
  simp only [rootOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd
  simp only [ACC] at h2
  rw [show a - (base + BitVec.ofNat 64 d) = (a - base) - BitVec.ofNat 64 d by
    exact Offset.sub_add_eq a base _]
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  simp only [ofs] at h1 h2
  have : (a - base).toNat < 2 ^ 64 := (a - base).isLt
  omega

/-- An inlined chain that stores only where `rootOk` allows. -/
theorem PSpec.of_ispec {base : Addr} {c : Prog isa} {f : Env → Env} (h : ISpec base c f)
    (hst : ∀ i ∈ instrs c, storesAt rootOk i = true) : PSpec base c f := fun s hs hb =>
  WP.mono (WP.storeFrame hst (h s hs hb)) fun t ⟨⟨tk, tb, te⟩, _, tf⟩ =>
    ⟨tk.regs.mono fun r hr => List.mem_cons_of_mem _ hr, tb, te,
      outside2_of_rootOk (by rw [hs.x3] at tf; exact tf)⟩

/-- A call of `vg_gf448_r56_mul` writing one of slots 14–21. -/
theorem mulCallP (base : Addr) (o a b : Index) (hob : o ≠ b) (ho : 14 ≤ o.val) :
    PSpec base (Point56.mulCall (slot o.val) (slot a.val) (slot b.val)) (applyOps [.mul o a b]) :=
  fun s hs hb => WP.mono (mulCallE hs hb o a b hob) fun t ⟨tk, _, _, tm, tb, _, _, te⟩ =>
    ⟨tk.mono fun r hr => by
        simp only [List.mem_cons] at hr ⊢
        rcases hr with h | h | h
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h),
      tb, te, fun p h1 h2 => tm p (by have := o.isLt; simp only [slot]; omega)
        (by simp only [ACC] at h2 ⊢; omega)⟩

end VG.Proof.Ed448.AArch64.Point56
