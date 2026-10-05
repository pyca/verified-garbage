import VerifiedGarbage.Proof.Curve448.AArch64.Square
import VerifiedGarbage.Proof.X448.AArch64.Main
import VerifiedGarbage.Impl.X448.AArch64.Weak
import VerifiedGarbage.Proof.X448.Encoding

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Weak.Env`. -/
section

/-!
# X448 on AArch64: the working space as field-element slots

Untrusted: everything here is checked by Lean. Field operations update one
of twenty-two slots, preserving bounded limbs in every slot. The frame
excludes saved registers, the swap bit and the scalar's decoded bits.
-/

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.Curve448.AArch64
open VG.Impl.X448.AArch64.Weak
abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe :=
  VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (limbs m base o) 8)
abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat := VG.Proof.X448.Wide.valN (limbs m base o) 8
abbrev Bounded := VG.Proof.Curve448.AArch64.Bounded
abbrev valN := VG.Proof.X448.Wide.valN
theorem valN_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = g i) :
    VG.Proof.X448.Wide.valN f n = VG.Proof.X448.Wide.valN g n := VG.Proof.X448.Wide.valN_congr h

abbrev Index := Fin 22
abbrev Env := VG.Proof.X448.AArch64.Weak.Index → Spec.X448.Fe

def E (m : Mem) (base : Addr) (i : VG.Proof.X448.AArch64.Weak.Index) : Spec.X448.Fe := VG.Proof.X448.AArch64.Weak.F m base (slot i.val)
def BoundedEnv (m : Mem) (base : Addr) : Prop := ∀ i : VG.Proof.X448.AArch64.Weak.Index, VG.Proof.X448.AArch64.Weak.Bounded m base (slot i.val)

abbrev workRegs := VG.Proof.X448.AArch64.workRegs
abbrev Keep := VG.Proof.X448.AArch64.Keep

theorem slot_bound (i : VG.Proof.X448.AArch64.Weak.Index) : VG.Proof.X448.AArch64.Slot (slot i.val) := by
  simp only [VG.Proof.X448.AArch64.Slot, slot, ACC]
  have := i.isLt
  omega

theorem slot_aligned (i : VG.Proof.X448.AArch64.Weak.Index) : slot i.val % 8 = 0 := by
  simp only [slot]; omega

theorem slot_sep {i j : VG.Proof.X448.AArch64.Weak.Index} (h : i ≠ j) : slot i.val + 128 ≤ slot j.val ∨ slot j.val + 128 ≤ slot i.val := by
  have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
  simp only [slot]
  omega

theorem E_update {base : Addr} {m m' : Mem} {o : VG.Proof.X448.AArch64.Weak.Index} (h : FieldMem base (slot o.val) m m') :
    VG.Proof.X448.AArch64.Weak.E m' base = Function.update (VG.Proof.X448.AArch64.Weak.E m base) o (VG.Proof.X448.AArch64.Weak.F m' base (slot o.val)) := by
  funext i
  by_cases hi : i = o
  · subst i; simp only [Function.update_self, VG.Proof.X448.AArch64.Weak.E]
  · rw [Function.update_of_ne hi]
    simp only [VG.Proof.X448.AArch64.Weak.E, VG.Proof.X448.AArch64.Weak.F]
    exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.AArch64.Weak.valN_congr (fun j hj =>
      h.limbs (VG.Proof.X448.AArch64.Weak.slot_sep hi) (VG.Proof.X448.AArch64.Weak.slot_bound i) (by omega : j < 16)))

theorem bounded_update {base : Addr} {m m' : Mem} {o : VG.Proof.X448.AArch64.Weak.Index} (h : FieldMem base (slot o.val) m m')
    (hm : VG.Proof.X448.AArch64.Weak.BoundedEnv m base) (ho : VG.Proof.X448.AArch64.Weak.Bounded m' base (slot o.val)) : VG.Proof.X448.AArch64.Weak.BoundedEnv m' base := by
  intro i
  by_cases hi : i = o
  · subst i; exact ho
  · intro j hj
    rw [h.limbs (VG.Proof.X448.AArch64.Weak.slot_sep hi) (VG.Proof.X448.AArch64.Weak.slot_bound i) (by omega : j < 16)]
    exact hm i j hj

def opMul (o a b : VG.Proof.X448.AArch64.Weak.Index) (e : VG.Proof.X448.AArch64.Weak.Env) : VG.Proof.X448.AArch64.Weak.Env := Function.update e o (e a * e b)
def opAdd (o a b : VG.Proof.X448.AArch64.Weak.Index) (e : VG.Proof.X448.AArch64.Weak.Env) : VG.Proof.X448.AArch64.Weak.Env := Function.update e o (e a + e b)
def opSub (o a b : VG.Proof.X448.AArch64.Weak.Index) (e : VG.Proof.X448.AArch64.Weak.Env) : VG.Proof.X448.AArch64.Weak.Env := Function.update e o (e a - e b)
def opA24 (o a : VG.Proof.X448.AArch64.Weak.Index) (e : VG.Proof.X448.AArch64.Weak.Env) : VG.Proof.X448.AArch64.Weak.Env := Function.update e o (Spec.X448.a24 * e a)
def opCopy (o a : VG.Proof.X448.AArch64.Weak.Index) (e : VG.Proof.X448.AArch64.Weak.Env) : VG.Proof.X448.AArch64.Weak.Env := Function.update e o (e a)
def opSwap (x y : VG.Proof.X448.AArch64.Weak.Index) (sw : Bool) (e : VG.Proof.X448.AArch64.Weak.Env) : VG.Proof.X448.AArch64.Weak.Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

theorem mulE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Weak.BoundedEnv s.mem base) (o a b : VG.Proof.X448.AArch64.Weak.Index) :
    WP isa (Impl.Curve448.AArch64.mul (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      VG.Proof.X448.AArch64.Weak.Keep base s t ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = VG.Proof.X448.AArch64.Weak.opMul o a b (VG.Proof.X448.AArch64.Weak.E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.mul_ok hs (VG.Proof.X448.AArch64.Weak.slot_bound o) (VG.Proof.X448.AArch64.Weak.slot_aligned o) (VG.Proof.X448.AArch64.Weak.slot_bound a) (VG.Proof.X448.AArch64.Weak.slot_aligned a) (VG.Proof.X448.AArch64.Weak.slot_bound b) (VG.Proof.X448.AArch64.Weak.slot_aligned b) (hb a) (hb b)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.AArch64.Weak.bounded_update h.mem hb bo, by
      have e' : VG.Proof.X448.AArch64.Weak.F t.mem base (slot o.val) = VG.Proof.X448.AArch64.Weak.F s.mem base (slot a.val) * VG.Proof.X448.AArch64.Weak.F s.mem base (slot b.val) := e
      rw [VG.Proof.X448.AArch64.Weak.E_update h.mem, e']; rfl⟩

theorem addE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Weak.BoundedEnv s.mem base) (o a b : VG.Proof.X448.AArch64.Weak.Index) :
    WP isa (.block (Impl.Curve448.AArch64.add (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      VG.Proof.X448.AArch64.Weak.Keep base s t ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = VG.Proof.X448.AArch64.Weak.opAdd o a b (VG.Proof.X448.AArch64.Weak.E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.add_ok hs (VG.Proof.X448.AArch64.Weak.slot_bound o) (VG.Proof.X448.AArch64.Weak.slot_aligned o) (VG.Proof.X448.AArch64.Weak.slot_bound a) (VG.Proof.X448.AArch64.Weak.slot_aligned a) (VG.Proof.X448.AArch64.Weak.slot_bound b) (VG.Proof.X448.AArch64.Weak.slot_aligned b) (hb a) (hb b)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.AArch64.Weak.bounded_update h.mem hb bo, by
      have e' : VG.Proof.X448.AArch64.Weak.F t.mem base (slot o.val) = VG.Proof.X448.AArch64.Weak.F s.mem base (slot a.val) + VG.Proof.X448.AArch64.Weak.F s.mem base (slot b.val) := e
      rw [VG.Proof.X448.AArch64.Weak.E_update h.mem, e']; rfl⟩

theorem subE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Weak.BoundedEnv s.mem base) (o a b : VG.Proof.X448.AArch64.Weak.Index) :
    WP isa (.block (Impl.Curve448.AArch64.sub (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      VG.Proof.X448.AArch64.Weak.Keep base s t ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = VG.Proof.X448.AArch64.Weak.opSub o a b (VG.Proof.X448.AArch64.Weak.E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.sub_ok hs (VG.Proof.X448.AArch64.Weak.slot_bound o) (VG.Proof.X448.AArch64.Weak.slot_aligned o) (VG.Proof.X448.AArch64.Weak.slot_bound a) (VG.Proof.X448.AArch64.Weak.slot_aligned a) (VG.Proof.X448.AArch64.Weak.slot_bound b) (VG.Proof.X448.AArch64.Weak.slot_aligned b) (hb a) (hb b)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.AArch64.Weak.bounded_update h.mem hb bo, by
      have e' : VG.Proof.X448.AArch64.Weak.F t.mem base (slot o.val) = VG.Proof.X448.AArch64.Weak.F s.mem base (slot a.val) - VG.Proof.X448.AArch64.Weak.F s.mem base (slot b.val) := e
      rw [VG.Proof.X448.AArch64.Weak.E_update h.mem, e']; rfl⟩

theorem a24E {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Weak.BoundedEnv s.mem base) (o a : VG.Proof.X448.AArch64.Weak.Index) :
    WP isa (.block (Impl.Curve448.AArch64.small (slot o.val) (slot a.val))) s fun t =>
      VG.Proof.X448.AArch64.Weak.Keep base s t ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = VG.Proof.X448.AArch64.Weak.opA24 o a (VG.Proof.X448.AArch64.Weak.E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.small_ok hs (VG.Proof.X448.AArch64.Weak.slot_bound o) (VG.Proof.X448.AArch64.Weak.slot_aligned o) (VG.Proof.X448.AArch64.Weak.slot_bound a) (VG.Proof.X448.AArch64.Weak.slot_aligned a) (hb a)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.AArch64.Weak.bounded_update h.mem hb bo, by
      have e' : VG.Proof.X448.AArch64.Weak.F t.mem base (slot o.val) = Spec.X448.a24 * VG.Proof.X448.AArch64.Weak.F s.mem base (slot a.val) := e
      rw [VG.Proof.X448.AArch64.Weak.E_update h.mem, e']; rfl⟩

theorem copyE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Weak.BoundedEnv s.mem base) (o a : VG.Proof.X448.AArch64.Weak.Index) :
    WP isa (.block (Impl.Curve448.AArch64.copy (slot o.val) (slot a.val))) s fun t =>
      VG.Proof.X448.AArch64.Weak.Keep base s t ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = VG.Proof.X448.AArch64.Weak.opCopy o a (VG.Proof.X448.AArch64.Weak.E s.mem base) := by
  have sep : slot o.val = slot a.val ∨ slot o.val + 128 ≤ slot a.val ∨ slot a.val + 128 ≤ slot o.val := by
    by_cases h : o = a
    · subst o; exact Or.inl rfl
    · exact Or.inr (VG.Proof.X448.AArch64.Weak.slot_sep h)
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs (Nat.le_trans (VG.Proof.X448.AArch64.Weak.slot_bound o) (by decide))
    (Nat.le_trans (VG.Proof.X448.AArch64.Weak.slot_bound a) (by decide)) (VG.Proof.X448.AArch64.Weak.slot_aligned o) (VG.Proof.X448.AArch64.Weak.slot_aligned a) sep) fun t ⟨tf, tm, tk⟩ => ?_
  have op : VG.Proof.X448.AArch64.Op base (slot o.val) s t := ⟨tk, FieldMem.output tm⟩
  refine ⟨op.keep, VG.Proof.X448.AArch64.Weak.bounded_update op.mem hb (fun i hi => ?_), ?_⟩
  · rw [tf i hi]; exact hb a i hi
  · rw [VG.Proof.X448.AArch64.Weak.E_update op.mem, show VG.Proof.X448.AArch64.Weak.F t.mem base (slot o.val) = VG.Proof.X448.AArch64.Weak.F s.mem base (slot a.val) from
      congrArg VG.Proof.X448.toFe (VG.Proof.X448.AArch64.Weak.valN_congr tf)]
    rfl

theorem cswapE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Weak.BoundedEnv s.mem base)
    (x y : VG.Proof.X448.AArch64.Weak.Index) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .x6 = VG.Proof.X448.AArch64.mask sw) :
    WP isa (.block (Impl.Curve448.AArch64.cswap (slot x.val) (slot y.val))) s fun t =>
      VG.Proof.X448.AArch64.Weak.Keep base s t ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv t.mem base ∧ t.gpr .x6 = s.gpr .x6 ∧
      VG.Proof.X448.AArch64.Weak.E t.mem base = VG.Proof.X448.AArch64.Weak.opSwap x y sw (VG.Proof.X448.AArch64.Weak.E s.mem base) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.cswap_ok hs (VG.Proof.X448.AArch64.Weak.slot_bound x) (VG.Proof.X448.AArch64.Weak.slot_bound y) (VG.Proof.X448.AArch64.Weak.slot_aligned x) (VG.Proof.X448.AArch64.Weak.slot_aligned y) (VG.Proof.X448.AArch64.Weak.slot_sep hxy) hm)
    fun t ⟨tx, ty, tm, tk⟩ => ?_
  have other : ∀ i : VG.Proof.X448.AArch64.Weak.Index, i ≠ x → i ≠ y → ∀ j < 8,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i hix hiy j hj
    have ex := VG.Proof.X448.AArch64.Weak.slot_sep hix
    have ey := VG.Proof.X448.AArch64.Weak.slot_sep hiy
    have hi := VG.Proof.X448.AArch64.Weak.slot_bound i
    change (word t.mem base (slot i.val + 8 * j)).toNat = _
    rw [tm.word (by omega) (by omega) (by change slot i.val + 128 ≤ 3584 at hi; omega)]
  have fx : VG.Proof.X448.AArch64.Weak.E t.mem base x = if sw then VG.Proof.X448.AArch64.Weak.E s.mem base y else VG.Proof.X448.AArch64.Weak.E s.mem base x := by
    cases sw <;> apply congrArg VG.Proof.X448.toFe <;> apply VG.Proof.X448.AArch64.Weak.valN_congr <;> exact tx
  have fy : VG.Proof.X448.AArch64.Weak.E t.mem base y = if sw then VG.Proof.X448.AArch64.Weak.E s.mem base x else VG.Proof.X448.AArch64.Weak.E s.mem base y := by
    cases sw <;> apply congrArg VG.Proof.X448.toFe <;> apply VG.Proof.X448.AArch64.Weak.valN_congr <;> exact ty
  refine ⟨⟨tk.mono ?_, ?_⟩, ?_, tk.1 _ (by decide), ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro p hp _
    have hx := x.isLt
    have hy := y.isLt
    apply tm p <;> simp only [slot] <;> omega
  · intro i j hj
    by_cases hix : i = x
    · subst i; rw [tx j hj]; cases sw <;> exact hb _ j hj
    · by_cases hiy : i = y
      · subst i; rw [ty j hj]; cases sw <;> exact hb _ j hj
      · rw [other i hix hiy j hj]; exact hb i j hj
  · funext i
    by_cases hiy : i = y
    · subst i; rw [VG.Proof.X448.AArch64.Weak.opSwap, Function.update_self]; exact fy
    · rw [VG.Proof.X448.AArch64.Weak.opSwap, Function.update_of_ne hiy]
      by_cases hix : i = x
      · subst i; rw [Function.update_self]; exact fx
      · rw [Function.update_of_ne hix]
        exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.AArch64.Weak.valN_congr (other i hix hiy))

end VG.Proof.X448.AArch64.Weak

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Weak.Ops`. -/
section

/-!
# X448 on AArch64: sequences of field operations

Untrusted: everything here is checked by Lean. Slot-indexed operations
interpret the implementation's field-operation lists as environment updates.
-/

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Impl.X448.AArch64.Weak

inductive FieldOp
  | mul (o a b : VG.Proof.X448.AArch64.Weak.Index)
  | add (o a b : VG.Proof.X448.AArch64.Weak.Index)
  | sub (o a b : VG.Proof.X448.AArch64.Weak.Index)
  | mulSmall (o a : VG.Proof.X448.AArch64.Weak.Index)
  | copy (o a : VG.Proof.X448.AArch64.Weak.Index)
  deriving DecidableEq

def FieldOp.impl : VG.Proof.X448.AArch64.Weak.FieldOp → Impl.X448.AArch64.Op
  | .mul o a b => .mul (slot o.val) (slot a.val) (slot b.val)
  | .add o a b => .add (slot o.val) (slot a.val) (slot b.val)
  | .sub o a b => .sub (slot o.val) (slot a.val) (slot b.val)
  | .mulSmall o a => .mulSmall (slot o.val) (slot a.val)
  | .copy o a => .copy (slot o.val) (slot a.val)

def FieldOp.apply : VG.Proof.X448.AArch64.Weak.FieldOp → VG.Proof.X448.AArch64.Weak.Env → VG.Proof.X448.AArch64.Weak.Env
  | .mul o a b => VG.Proof.X448.AArch64.Weak.opMul o a b
  | .add o a b => VG.Proof.X448.AArch64.Weak.opAdd o a b
  | .sub o a b => VG.Proof.X448.AArch64.Weak.opSub o a b
  | .mulSmall o a => VG.Proof.X448.AArch64.Weak.opA24 o a
  | .copy o a => VG.Proof.X448.AArch64.Weak.opCopy o a

def applyOps : List VG.Proof.X448.AArch64.Weak.FieldOp → VG.Proof.X448.AArch64.Weak.Env → VG.Proof.X448.AArch64.Weak.Env
  | [], e => e
  | op :: rest, e => VG.Proof.X448.AArch64.Weak.applyOps rest (op.apply e)

theorem fieldOp_ok {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Weak.BoundedEnv s.mem base) (op : VG.Proof.X448.AArch64.Weak.FieldOp) :
    WP isa (Impl.X448.AArch64.Weak.code op.impl) s fun t =>
      VG.Proof.X448.AArch64.Weak.Keep base s t ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = op.apply (VG.Proof.X448.AArch64.Weak.E s.mem base) := by
  cases op with
  | mul o a b => exact VG.Proof.X448.AArch64.Weak.mulE hs hb o a b
  | add o a b => exact VG.Proof.X448.AArch64.Weak.addE hs hb o a b
  | sub o a b => exact VG.Proof.X448.AArch64.Weak.subE hs hb o a b
  | mulSmall o a => exact VG.Proof.X448.AArch64.Weak.a24E hs hb o a
  | copy o a => exact VG.Proof.X448.AArch64.Weak.copyE hs hb o a

theorem ops_ok {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Weak.BoundedEnv s.mem base) (xs : List VG.Proof.X448.AArch64.Weak.FieldOp) :
    WP isa (ops (xs.map FieldOp.impl)) s fun t =>
      VG.Proof.X448.AArch64.Weak.Keep base s t ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = VG.Proof.X448.AArch64.Weak.applyOps xs (VG.Proof.X448.AArch64.Weak.E s.mem base) := by
  induction xs generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hb, rfl⟩
  | cons op rest ih =>
    change WP isa (.seq (Impl.X448.AArch64.Weak.code op.impl) (ops (rest.map FieldOp.impl))) s _
    rw [WP.seq_iff]
    refine WP.mono (VG.Proof.X448.AArch64.Weak.fieldOp_ok hs hb op) fun t ⟨tk, tb, te⟩ => ?_
    refine WP.mono (ih (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, ?_⟩
    rw [ue, te]
    rfl

/-- The arithmetic part of one Montgomery-ladder step. -/
def stepFields : List VG.Proof.X448.AArch64.Weak.FieldOp :=
  [.add 5 1 2, .mul 9 5 5, .sub 6 1 2, .mul 10 6 6, .sub 11 9 10,
    .add 7 3 4, .sub 8 3 4, .mul 12 8 5, .mul 13 7 6,
    .add 3 12 13, .mul 3 3 3, .sub 4 12 13, .mul 4 4 4, .mul 4 0 4,
    .mul 1 9 10, .mulSmall 2 11, .add 2 9 2, .mul 2 11 2]

theorem stepFields_impl : stepFields.map FieldOp.impl = stepOps := by decide +kernel

end VG.Proof.X448.AArch64.Weak

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Weak.BitStep`. -/
section

/-!
# X448 on AArch64: reading a scalar bit

Untrusted: everything here is checked by Lean. The public counter selects a
byte of the scalar-bit array. Only the XOR mask, never control flow, depends
on that bit and the previous swap bit.
-/

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Impl.X448.AArch64.Weak

/-- The start of `step`. -/
def stepPre : List Instr :=
  [.subImm .x .x19 .x19 1, .add .x .x11 .x3 .x19, .ldrb .x4 .x11 BITS,
    ld .x5 SWAP, .logic .eor .x .x5 .x5 .x4, st .x4 SWAP,
    .movz .x .x6 0 0, .sub .x .x6 .x6 .x5]

theorem mask_xor : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 64) - (BitVec.ofNat 64 a ^^^ (BitVec.ofNat 8 b).setWidth 64) =
      VG.Proof.X448.AArch64.mask (decide (a ^^^ b = 1)) := by decide

theorem stepPre_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 448)
    (hb : s.gpr .x19 = BitVec.ofNat 64 (t + 1)) {kt sw0 : Nat} (hk : kt < 2) (hsw : sw0 < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 kt)
    (hswap : word s.mem base SWAP = BitVec.ofNat 64 sw0) :
    WP isa (.block VG.Proof.X448.AArch64.Weak.stepPre) s fun s' =>
      s'.gpr .x19 = BitVec.ofNat 64 t ∧ s'.gpr .x6 = VG.Proof.X448.AArch64.mask (decide (sw0 ^^^ kt = 1)) ∧
      (∀ r, r ∉ [.x19, .x4, .x5, .x6, .x11] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off base SWAP) (BitVec.ofNat 64 kt) := by
  have hb' : s.gpr .x19 - BitVec.ofNat 64 1 = BitVec.ofNat 64 t := by
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hin : InRegions (s.rd ++ s.wr) (off base (BITS + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have hw : InRegions s.wr (off base SWAP) 8 := ⟨_, hs.wr, contains_sc (by simp only [SWAP]; omega)⟩
  have hr : InRegions (s.rd ++ s.wr) (off base SWAP) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [SWAP]; omega)⟩
  have enc : BITS % 1 = 0 ∧ BITS < 4096 * 1 := by decide
  have encSwap : SWAP % 8 = 0 ∧ SWAP < 4096 * 8 := by decide
  have hswap' : s.mem.readW (off base SWAP) 64 = BitVec.ofNat 64 sw0 := hswap
  apply WP.of_runBlock
  simp only [VG.Proof.X448.AArch64.Weak.stepPre, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Size.bytes, Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.mem_write, hb', hs.x3, addr, enc, encSwap, and_self,
    off, Offset.add_add, Nat.add_comm t BITS, State.load, State.store,
    hin, hr, hw, read1_eq, read8_eq, write8_eq, hbit, hswap',
    Option.bind_some, Option.map_some, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  have e0 : BitVec.setWidth 64 (0 : BitVec 16) = 0 := rfl
  have ext : (BitVec.setWidth 32 (BitVec.ofNat 8 kt)).setWidth 64 =
      (BitVec.ofNat 8 kt).setWidth 64 := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  simp only [ext]
  have ek : BitVec.setWidth 64 (BitVec.ofNat 8 kt) = BitVec.ofNat 64 kt := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  refine ⟨trivial, by rw [e0]; exact VG.Proof.X448.AArch64.Weak.mask_xor sw0 hsw kt hk, fun r hr => ?_, trivial, trivial,
    by rw [ek]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.X448.AArch64.Weak

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Weak.Counters`. -/
section

/-!
# X448 on AArch64: loop counters

Untrusted: everything here is checked by Lean. Setting and decrementing
public counters preserves memory and every other register.
-/

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64

/-- Set the ladder or squaring counter. -/
theorem setCounter_ok (s : State) (k : Nat) (hk : k < 2 ^ 16) :
    WP isa (.block [.movz .x .x19 (BitVec.ofNat 16 k) 0]) s fun s' =>
      s'.gpr .x19 = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .x19 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => by simp only [RegUpd.gpr_write, hr, ite_false], rfl, rfl, rfl⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega)]

/-- Decrement the counter; the result is zero precisely on the last iteration. -/
theorem decCounter_ok {s : State} {k : Nat} (hk : k < 2 ^ 16)
    (hb : s.gpr .x19 = BitVec.ofNat 64 (k + 1)) :
    WP isa (.block [.subImm .x .x19 .x19 1]) s fun s' =>
      s'.gpr .x19 = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .x19 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ (s'.gpr .x19 == 0) = decide (k = 0) := by
  have hb' : s.gpr .x19 - BitVec.ofNat 64 1 = BitVec.ofNat 64 k := by
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have zero : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rfl
    · rw [decide_eq_false (by omega)]
      apply beq_false_of_ne
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by simp; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true,
    State.read, BitVec.setWidth_eq, hb', RegUpd.gpr_write_self, zero,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [RegUpd.gpr_write, hr, ite_false], rfl, rfl, rfl, trivial⟩

end VG.Proof.X448.AArch64.Weak

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Weak.Iter`. -/
section

/-!
# X448 on AArch64: the Montgomery ladder

Untrusted: everything here is checked by Lean. Each iteration consumes one
scalar bit and updates the five field slots according to `ladderStep`.
-/

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Impl.X448.AArch64.Weak

def stepEnv (sw : Bool) (e : VG.Proof.X448.AArch64.Weak.Env) : VG.Proof.X448.AArch64.Weak.Env :=
  VG.Proof.X448.AArch64.Weak.applyOps VG.Proof.X448.AArch64.Weak.stepFields (VG.Proof.X448.AArch64.Weak.opSwap 2 4 sw (VG.Proof.X448.AArch64.Weak.opSwap 1 3 sw e))

theorem cswap_fst (sw : Nat) (a b : Spec.X448.Fe) :
    (Spec.X448.cswap sw a b).1 = if decide (sw = 1) = true then b else a := by
  simp only [Spec.X448.cswap, decide_eq_true_eq]; split <;> rfl

theorem cswap_snd (sw : Nat) (a b : Spec.X448.Fe) :
    (Spec.X448.cswap sw a b).2 = if decide (sw = 1) = true then a else b := by
  simp only [Spec.X448.cswap, decide_eq_true_eq]; split <;> rfl

theorem stepEnv_eval (e : VG.Proof.X448.AArch64.Weak.Env) (st : Spec.X448.Ladder) (k : Nat) (u : Spec.X448.Fe) (t : Nat)
    (h0 : e 0 = u) (h1 : e 1 = st.x2) (h2 : e 2 = st.z2) (h3 : e 3 = st.x3) (h4 : e 4 = st.z3) :
    VG.Proof.X448.AArch64.Weak.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 0 = u ∧
    VG.Proof.X448.AArch64.Weak.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 1 = (Spec.X448.ladderStep k u st t).x2 ∧
    VG.Proof.X448.AArch64.Weak.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 2 = (Spec.X448.ladderStep k u st t).z2 ∧
    VG.Proof.X448.AArch64.Weak.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 3 = (Spec.X448.ladderStep k u st t).x3 ∧
    VG.Proof.X448.AArch64.Weak.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 4 = (Spec.X448.ladderStep k u st t).z3 := by
  rw [VG.Proof.X448.ladderStep_eq]
  simp only [↓reduceIte, VG.Proof.X448.AArch64.Weak.stepEnv, VG.Proof.X448.AArch64.Weak.applyOps, VG.Proof.X448.AArch64.Weak.stepFields, FieldOp.apply,
    VG.Proof.X448.AArch64.Weak.opMul, VG.Proof.X448.AArch64.Weak.opAdd, VG.Proof.X448.AArch64.Weak.opSub, VG.Proof.X448.AArch64.Weak.opA24, VG.Proof.X448.AArch64.Weak.opSwap, Function.update_apply,
    VG.Proof.X448.AArch64.Weak.cswap_fst, VG.Proof.X448.AArch64.Weak.cswap_snd, h0, h1, h2, h3, h4]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem swaps_ok {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Weak.BoundedEnv s.mem base)
    {sw : Bool} (hm : s.gpr .x6 = VG.Proof.X448.AArch64.mask sw) :
    WP isa (.block (VG.Impl.X448.AArch64.Weak.cswap X2 X3 ++ VG.Impl.X448.AArch64.Weak.cswap Z2 Z3)) s fun t =>
      VG.Proof.X448.AArch64.Weak.Keep base s t ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = VG.Proof.X448.AArch64.Weak.opSwap 2 4 sw (VG.Proof.X448.AArch64.Weak.opSwap 1 3 sw (VG.Proof.X448.AArch64.Weak.E s.mem base)) := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.cswapE hs hb 1 3 (by decide) hm) fun t ⟨tk, tb, tc, te⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.Weak.cswapE (tk.scr hs) tb 2 4 (by decide) (tc.trans hm)) fun u ⟨uk, ub, _, ue⟩ =>
    ⟨tk.trans uk, ub, by rw [ue, te]⟩

theorem counter_zero {s : State} {n : Nat} (hn : n < 2 ^ 32)
    (hc : s.gpr .x19 = BitVec.ofNat 64 n) : (s.gpr .x19 == 0) = decide (n = 0) := by
  rw [hc]
  rcases Nat.eq_zero_or_pos n with rfl | h
  · rfl
  · rw [decide_eq_false (by omega)]
    apply beq_false_of_ne
    intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    exact absurd this (by simp; omega)

/-- The complete loop invariant, including its memory frame. -/
structure LInv (base : Addr) (k : Nat) (u : Spec.X448.Fe) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  bounded : VG.Proof.X448.AArch64.Weak.BoundedEnv s.mem base
  regs : Keeps (.x19 :: VG.Proof.X448.AArch64.Weak.workRegs) s₀ s
  x19 : s.gpr .x19 = BitVec.ofNat 64 n
  mem : Outside2 base 16 2864 ACC 512 s₀.mem s.mem
  x1 : VG.Proof.X448.AArch64.Weak.E s.mem base 0 = u
  x2 : VG.Proof.X448.AArch64.Weak.E s.mem base 1 = (VG.Proof.X448.ladderAfter k u n).x2
  z2 : VG.Proof.X448.AArch64.Weak.E s.mem base 2 = (VG.Proof.X448.ladderAfter k u n).z2
  x3 : VG.Proof.X448.AArch64.Weak.E s.mem base 3 = (VG.Proof.X448.ladderAfter k u n).x3
  z3 : VG.Proof.X448.AArch64.Weak.E s.mem base 4 = (VG.Proof.X448.ladderAfter k u n).z3
  swap : word s.mem base SWAP = BitVec.ofNat 64 (VG.Proof.X448.ladderAfter k u n).swap

theorem ofs_off' (base : Addr) {d : Nat} (h : d < 2 ^ 64) : ofs base (off base d) = d :=
  Mem.sub_ofNat_toNat base h

theorem step_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe} {n : Nat} (hn : n < 448)
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t))
    (hi : VG.Proof.X448.AArch64.Weak.LInv base k u s₀ s (n + 1)) :
    WP isa VG.Impl.X448.AArch64.Weak.step s fun t => VG.Proof.X448.AArch64.Weak.LInv base k u s₀ t n ∧ (t.gpr .x19 == 0) = decide (n = 0) := by
  have hs := hi.scr
  have bitval : s.mem (off base (BITS + n)) = BitVec.ofNat 8 (VG.Proof.X448.bit k n) := by
    rw [hi.mem _ (by rw [VG.Proof.X448.AArch64.Weak.ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
      (by rw [VG.Proof.X448.AArch64.Weak.ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)]
    exact hbits n hn
  rw [VG.Impl.X448.AArch64.Weak.step, WP.seq_iff,
    show stepHead = VG.Proof.X448.AArch64.Weak.stepPre ++ (VG.Impl.X448.AArch64.Weak.cswap X2 X3 ++ VG.Impl.X448.AArch64.Weak.cswap Z2 Z3) by
      simp only [stepHead, VG.Proof.X448.AArch64.Weak.stepPre, List.append_assoc], WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.stepPre_ok hs hn hi.x19 (by have := VG.Proof.X448.bit_le k n; omega)
    (by have := VG.Proof.X448.ladderAfter_swap_le k u (n := n + 1) (by omega); omega) bitval hi.swap)
    fun s₁ ⟨b₁, c₁, g₁, rd₁, wr₁, m₁⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨(g₁ _ (by decide)).trans hs.x3, (g₁ _ (by decide)).trans hs.mask, wr₁ ▸ hs.wr, hs.nowrap⟩
  have out₁ : Outside base SWAP 8 s.mem s₁.mem := by
    rw [m₁]; exact writeW_outside _ _ _ (by decide)
  have l₁ : ∀ i : VG.Proof.X448.AArch64.Weak.Index, ∀ j < 8, limbs s₁.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i j hj
    exact out₁.limbs (Or.inr (by simp only [slot, SWAP]; omega))
      (Nat.le_trans (VG.Proof.X448.AArch64.Weak.slot_bound i) (by decide)) (by omega)
  have e₁ : VG.Proof.X448.AArch64.Weak.E s₁.mem base = VG.Proof.X448.AArch64.Weak.E s.mem base := by
    funext i; exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.AArch64.Weak.valN_congr (l₁ i))
  have bb₁ : VG.Proof.X448.AArch64.Weak.BoundedEnv s₁.mem base := by
    intro i j hj; rw [l₁ i j hj]; exact hi.bounded i j hj
  refine WP.mono (VG.Proof.X448.AArch64.Weak.swaps_ok hs₁ bb₁ c₁) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_
  rw [← VG.Proof.X448.AArch64.Weak.stepFields_impl]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.ops_ok (k₂.scr hs₁) bb₂ VG.Proof.X448.AArch64.Weak.stepFields) fun s₃ ⟨k₃, bb₃, e₃⟩ => ?_
  have core := k₂.trans k₃
  have b₃ : s₃.gpr .x19 = BitVec.ofNat 64 n := (core.regs.1 _ (by decide)).trans b₁
  have vals := VG.Proof.X448.AArch64.Weak.stepEnv_eval (VG.Proof.X448.AArch64.Weak.E s.mem base) (VG.Proof.X448.ladderAfter k u (n + 1)) k u n
    hi.x1 hi.x2 hi.z2 hi.x3 hi.z3
  have e₄ : VG.Proof.X448.AArch64.Weak.E s₃.mem base = VG.Proof.X448.AArch64.Weak.stepEnv (decide ((VG.Proof.X448.ladderAfter k u (n + 1)).swap ^^^ VG.Proof.X448.bit k n = 1))
      (VG.Proof.X448.AArch64.Weak.E s.mem base) := by rw [e₃, e₂, e₁]; rfl
  rw [← VG.Proof.X448.ladderAfter_step k u hn, ← e₄] at vals
  refine ⟨⟨core.scr hs₁, bb₃, ?_, b₃, ?_, vals.1, vals.2.1, vals.2.2.1,
    vals.2.2.2.1, vals.2.2.2.2, ?_⟩, VG.Proof.X448.AArch64.Weak.counter_zero (by omega) b₃⟩
  · refine hi.regs.trans ⟨?_, core.regs.2.1.trans rd₁, core.regs.2.2.trans wr₁⟩
    intro r hr
    have hwork : r ∉ VG.Proof.X448.AArch64.Weak.workRegs := fun h => hr (List.mem_cons_of_mem _ h)
    have hpre : r ∉ [Reg.x19, .x4, .x5, .x6, .x11] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hr (by subst r; decide), fun h => hr (by subst r; decide),
        fun h => hr (by subst r; decide), fun h => hr (by subst r; decide),
        fun h => hr (by subst r; decide)⟩
    rw [core.regs.1 r hwork, g₁ r hpre]
  · refine hi.mem.trans ?_
    intro p hp hq
    rw [core.mem p (by omega) hq, out₁ p (by simp only [SWAP]; omega)]
  · rw [core.mem.word (by simp only [SWAP]; omega) (by simp only [SWAP, ACC]; omega) (by decide),
      m₁, VG.Proof.X448.ladderAfter_step k u hn]
    exact Mem.readW_writeW_self64 _ _ _

end VG.Proof.X448.AArch64.Weak

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Weak.FinalSwap`. -/
section

/-!
# X448 on AArch64: the swap after the ladder

Untrusted: everything here is checked by Lean. The final swap bit selects
the coordinates to be converted back to affine form.
-/

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Impl.X448.AArch64.Weak

theorem mask_of : ∀ a < 2, BitVec.setWidth 64 (0 : BitVec 16) - BitVec.ofNat 64 a =
    VG.Proof.X448.AArch64.mask (decide (a = 1)) := by decide

theorem swapMask_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Nat} (hsw : sw < 2)
    (hw : word s.mem base SWAP = BitVec.ofNat 64 sw) :
    WP isa (.block [ld .x5 SWAP, .movz .x .x6 0 0, .sub .x .x6 .x6 .x5]) s
      fun t => t.gpr .x6 = VG.Proof.X448.AArch64.mask (decide (sw = 1)) ∧ t.mem = s.mem ∧ Keeps [.x5, .x6] s t := by
  have hr := hs.read (d := SWAP) (n := 8) (by decide)
  have enc : SWAP % 8 = 0 ∧ SWAP < 32768 := by decide
  have hw' : s.mem.readW (off base SWAP) 64 = BitVec.ofNat 64 sw := hw
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    BitVec.setWidth_eq, enc, and_self,
    hs.x3, hr, read8_eq, hw', Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.X448.AArch64.Weak.mask_of sw hsw, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem lastSwap_ok {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Weak.BoundedEnv s.mem base)
    {sw : Nat} (hsw : sw < 2) (hw : word s.mem base SWAP = BitVec.ofNat 64 sw) :
    WP isa (.block lastSwap) s fun t => VG.Proof.X448.AArch64.Weak.Keep base s t ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv t.mem base ∧
      VG.Proof.X448.AArch64.Weak.E t.mem base = VG.Proof.X448.AArch64.Weak.opSwap 2 4 (decide (sw = 1)) (VG.Proof.X448.AArch64.Weak.opSwap 1 3 (decide (sw = 1)) (VG.Proof.X448.AArch64.Weak.E s.mem base)) := by
  rw [lastSwap, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.swapMask_ok hs hsw hw) fun t ⟨tc, tm, tk⟩ => ?_
  have kt : VG.Proof.X448.AArch64.Weak.Keep base s t := ⟨tk.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide), tm ▸ Outside2.refl _ _ _ _ _ _⟩
  refine WP.mono (VG.Proof.X448.AArch64.Weak.swaps_ok (kt.scr hs) (tm ▸ hb) tc) fun u ⟨ku, bu, eu⟩ =>
    ⟨kt.trans ku, bu, by rw [eu, tm]⟩

end VG.Proof.X448.AArch64.Weak

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Weak.Setup`. -/
section

namespace VG.Proof.X448.AArch64.Weak
open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot ACC TMP SWAP)
open VG.Impl.X448.AArch64.Weak

/-- Convert each initialized field slot once, preserving the scalar and ABI saves. -/
theorem convert_ok {s : State} {base : Addr} (hs : Scr s base)
    (hb : VG.Proof.X448.AArch64.BoundedEnv s.mem base) :
    WP isa (.block convert) s fun t =>
      VG.Proof.X448.AArch64.Weak.Keep base s t ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = VG.Proof.X448.AArch64.E s.mem base := by
  let inv := fun n (t : State) => VG.Proof.X448.AArch64.Weak.Keep base s t ∧
    (∀ i : VG.Proof.X448.AArch64.Weak.Index, i.val < n → VG.Proof.X448.AArch64.Weak.Bounded t.mem base (slot i.val) ∧
      VG.Proof.X448.AArch64.Weak.E t.mem base i = VG.Proof.X448.AArch64.E s.mem base i) ∧
    (∀ i : VG.Proof.X448.AArch64.Weak.Index, n ≤ i.val → ∀ j < 16, limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j)
  have step : ∀ n t, n < 22 → inv n t →
      WP isa (.block (Impl.Curve448.AArch64.fromLegacy (slot n))) t (inv (n + 1)) := by
    intro n t hn ⟨tk, tv, tr⟩
    let o : VG.Proof.X448.AArch64.Weak.Index := ⟨n, hn⟩
    have ov : o.val = n := rfl
    have bo : VG.Proof.X448.AArch64.Bounded t.mem base (slot n) := by
      intro j hj; rw [tr o (by omega) j hj]; exact hb o j hj
    refine WP.mono (VG.Proof.Curve448.AArch64.fromLegacy_ok (tk.scr hs)
      (VG.Proof.X448.AArch64.Weak.slot_bound o) (VG.Proof.X448.AArch64.Weak.slot_aligned o) bo) fun u ⟨uk, ub, uv⟩ => ?_
    refine ⟨tk.trans (VG.Proof.X448.AArch64.Op.keep (o := o) uk), ?_, ?_⟩
    · intro i hi
      by_cases he : i = o
      · subst i
        refine ⟨ub, ?_⟩
        change VG.Proof.X448.AArch64.Weak.F u.mem base (slot n) = _
        have uv' : VG.Proof.X448.AArch64.Weak.F u.mem base (slot n) = VG.Proof.X448.AArch64.F t.mem base (slot n) := uv
        rw [uv']
        exact congrArg toFe (VG.Proof.X448.valN_congr (tr o (by omega)))
      · have sep := VG.Proof.X448.AArch64.Weak.slot_sep he
        have before : i.val < n := by have := i.isLt; have hne : i.val ≠ n := fun e => he (Fin.ext e); omega
        have old := tv i before
        refine ⟨?_, ?_⟩
        · intro j hj
          rw [uk.mem.limbs sep (VG.Proof.X448.AArch64.Weak.slot_bound i) (by omega : j < 16)]; exact old.1 j hj
        · exact (congrArg toFe (VG.Proof.Curve448.AArch64.field_fe uk.mem sep (VG.Proof.X448.AArch64.Weak.slot_bound i))).trans old.2
    · intro i hi j hj
      have he : i ≠ o := by intro e; subst i; change n + 1 ≤ n at hi; omega
      rw [uk.mem.limbs (VG.Proof.X448.AArch64.Weak.slot_sep he) (VG.Proof.X448.AArch64.Weak.slot_bound i) hj]
      exact tr i (by omega) j hj
  refine WP.mono (wp_range_flatMap (M := isa) (N := 22) inv step 22 (by decide) s
    ⟨Keep.refl _ _, fun i hi => by omega, fun _ _ _ _ => rfl⟩) fun t ⟨tk, tv, _⟩ => ?_
  exact ⟨tk, fun i => (tv i i.isLt).1, funext fun i => (tv i i.isLt).2⟩

def setupRegs : List Reg := .x20 :: .x12 :: VG.Proof.X448.AArch64.Weak.workRegs

theorem setup_ok {s : State} {base p : Addr} (hc : s.gpr .x3 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hp : s.gpr .x2 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block setup) s fun t =>
      Scr t base ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv t.mem base ∧ t.gpr .x20 = s.gpr .x0 ∧ Keeps VG.Proof.X448.AArch64.Weak.setupRegs s t ∧
      Outside base 0 8192 s.mem t.mem ∧ VG.Proof.X448.AArch64.Saved base s.gpr t.mem ∧
      VG.Proof.X448.AArch64.Weak.E t.mem base 0 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      VG.Proof.X448.AArch64.Weak.E t.mem base 1 = 1 ∧ VG.Proof.X448.AArch64.Weak.E t.mem base 2 = 0 ∧
      VG.Proof.X448.AArch64.Weak.E t.mem base 3 = VG.Proof.X448.AArch64.Weak.E t.mem base 0 ∧ VG.Proof.X448.AArch64.Weak.E t.mem base 4 = 1 ∧ word t.mem base SWAP = 0 := by
  rw [setup, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.setup_ok hc hw hn hp hr hd)
    fun u ⟨us, ub, up, uk, um, uv, u0, u1, u2, u3, u4, uw⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.Weak.convert_ok us ub) fun t ⟨tk, tb, te⟩ => ?_
  refine ⟨tk.scr us, tb, (tk.regs.1 _ (by decide)).trans up,
    (uk.mono (by decide)).trans (tk.regs.mono (by decide)),
    um.trans (tk.mem.whole (by decide) (by decide)),
    uv.outside2 tk.mem (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [te]; exact u0
  · rw [te]; exact u1
  · rw [te]; exact u2
  · rw [te]; exact u3
  · rw [te]; exact u4
  · rw [tk.mem.word (d := SWAP) (by decide) (by decide) (by decide)]; exact uw
end VG.Proof.X448.AArch64.Weak

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Weak.Finish`. -/
section

namespace VG.Proof.X448.AArch64.Weak
open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st X2 T7 ACC)
open VG.Impl.X448.AArch64.Weak
def finishRegs : List Reg := .x19 :: .x20 :: VG.Proof.X448.AArch64.Weak.workRegs

theorem finish_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Weak.BoundedEnv s.mem base)
    (hp : s.gpr .x1 = p) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) {g : Reg → BitVec 64} (sv : VG.Proof.X448.AArch64.Saved base g s.mem) :
    WP isa finish s fun t =>
      t.gpr .x19 = g .x19 ∧ t.gpr .x20 = g .x20 ∧ Keeps VG.Proof.X448.AArch64.Weak.finishRegs s t ∧
      Frame [⟨base, 8192⟩, ⟨p, 56⟩] s.mem t.mem ∧
      Spec.X448.bytesAt t.mem p 56 = Spec.X448.encodeUCoordinate (VG.Proof.X448.AArch64.Weak.E s.mem base 1 * VG.Proof.X448.AArch64.Weak.E s.mem base 21) := by
  refine WP.seq (WP.mono (VG.Proof.Curve448.AArch64.mul_ok hs (o := X2) (a := X2) (b := T7) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (hb 1) (hb 21)) fun u ⟨uk, ub, uv⟩ => ?_)
  have us₀ := hs.of_keeps uk.1 (by decide)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.toLegacy_ok us₀ (o := X2)
    (by decide) (by decide) ub) fun u' ⟨ck, cb, cv⟩ => ?_
  have uk : VG.Proof.X448.AArch64.Op base X2 s u' := ⟨uk.1.trans ck.1, uk.2.trans ck.2⟩
  have uv : VG.Proof.X448.AArch64.F u'.mem base X2 = VG.Proof.X448.AArch64.Weak.E s.mem base 1 * VG.Proof.X448.AArch64.Weak.E s.mem base 21 :=
    cv.trans uv
  have us := hs.of_keeps uk.1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok us cb) fun v ⟨vb, vv, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (output_ok vs vb ((vk.1 _ (by decide)).trans ((uk.1.1 _ (by decide)).trans hp))
    (by intro j hj; rw [vk.2.2, uk.1.2.2]; exact hw j hj) hfar) fun w ⟨wv, wm, wk⟩ => ?_
  have ws := vs.of_keeps wk (by decide)
  have svv := (sv.field uk.2 (by decide)).field vm (by decide)
  have svw : VG.Proof.X448.AArch64.Saved base g w.mem :=
    ⟨(output_word wm (by decide) (by decide) hfar).trans svv.1,
      (output_word wm (by decide) (by decide) hfar).trans svv.2⟩
  refine WP.mono (restore_ok ws svw) fun t ⟨tb, tr, tm, tk⟩ => ?_
  refine ⟨tb, tr, (uk.1.mono ?_).trans ((vk.mono ?_).trans ((wk.mono ?_).trans (tk.mono ?_))), ?_, ?_⟩
  · intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  · intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
  · intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  · rw [tm]
    exact (((uk.2.whole (by decide)).trans (vm.whole (by decide))).frame.mono (by simp)).trans
      (wm.frame.mono (by simp))
  · rw [tm, wv, vv, encodeUCoordinate_eq]
    refine congrArg (VG.Proof.X25519.leBytes 56) ?_
    exact congrArg Fin.val uv

end VG.Proof.X448.AArch64.Weak

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Weak.Square`. -/
section

/-!
# X448 on AArch64: runs of squarings

Untrusted: everything here is checked by Lean. The inversion reuses field
multiplication in a loop with its own counter. The field slots and memory
frame compose exactly as they do for straight-line operation lists.
-/

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Impl.X448.AArch64.Weak

structure IKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.x19 :: VG.Proof.X448.AArch64.Weak.workRegs) s t
  mem : Outside2 base 64 2816 ACC 512 s.mem t.mem

theorem IKeep.refl (base : Addr) (s : State) : VG.Proof.X448.AArch64.Weak.IKeep base s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem IKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.X448.AArch64.Weak.IKeep base s t) (h' : VG.Proof.X448.AArch64.Weak.IKeep base t u) :
    VG.Proof.X448.AArch64.Weak.IKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem IKeep.scr {base : Addr} {s t : State} (h : VG.Proof.X448.AArch64.Weak.IKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem Keep.ikeep {base : Addr} {s t : State} (h : VG.Proof.X448.AArch64.Weak.Keep base s t) : VG.Proof.X448.AArch64.Weak.IKeep base s t :=
  ⟨h.regs.mono (fun _ hr => List.mem_cons_of_mem _ hr), h.mem⟩

theorem counter_keep {base : Addr} {s t : State} (hg : ∀ r, r ≠ .x19 → t.gpr r = s.gpr r)
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : VG.Proof.X448.AArch64.Weak.IKeep base s t :=
  ⟨⟨fun r h => hg r (fun he => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
    hm ▸ Outside2.refl _ _ _ _ _ _⟩

def ISpec (base : Addr) (code : Prog isa) (f : VG.Proof.X448.AArch64.Weak.Env → VG.Proof.X448.AArch64.Weak.Env) : Prop :=
  ∀ s, Scr s base → VG.Proof.X448.AArch64.Weak.BoundedEnv s.mem base → WP isa code s fun t =>
    VG.Proof.X448.AArch64.Weak.IKeep base s t ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = f (VG.Proof.X448.AArch64.Weak.E s.mem base)

theorem ISpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : VG.Proof.X448.AArch64.Weak.Env → VG.Proof.X448.AArch64.Weak.Env}
    (h₁ : VG.Proof.X448.AArch64.Weak.ISpec base c₁ f) (h₂ : VG.Proof.X448.AArch64.Weak.ISpec base c₂ g) :
    VG.Proof.X448.AArch64.Weak.ISpec base (.seq c₁ c₂) (fun e => g (f e)) := fun s hs hb =>
  WP.seq (WP.mono (h₁ s hs hb) fun t ⟨tk, tb, te⟩ =>
    WP.mono (h₂ t (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, by rw [ue, te]⟩)

theorem opsI (base : Addr) (xs : List VG.Proof.X448.AArch64.Weak.FieldOp) :
    VG.Proof.X448.AArch64.Weak.ISpec base (ops (xs.map FieldOp.impl)) (VG.Proof.X448.AArch64.Weak.applyOps xs) := fun _ hs hb =>
  WP.mono (VG.Proof.X448.AArch64.Weak.ops_ok hs hb xs) fun _ ⟨tk, tb, te⟩ => ⟨tk.ikeep, tb, te⟩

def opSqn (o : VG.Proof.X448.AArch64.Weak.Index) (n : Nat) (e : VG.Proof.X448.AArch64.Weak.Env) : VG.Proof.X448.AArch64.Weak.Env := Function.update e o (Proof.X448.sqn (e o) n)

theorem opMul_update (o : VG.Proof.X448.AArch64.Weak.Index) (e : VG.Proof.X448.AArch64.Weak.Env) (v : Spec.X448.Fe) :
    VG.Proof.X448.AArch64.Weak.opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [VG.Proof.X448.AArch64.Weak.opMul, Function.update_self, Function.update_idem]

theorem sqnI (base : Addr) (o : VG.Proof.X448.AArch64.Weak.Index) {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 16) :
    VG.Proof.X448.AArch64.Weak.ISpec base (Impl.X448.AArch64.Weak.sqn (slot o.val) n) (VG.Proof.X448.AArch64.Weak.opSqn o n) := by
  intro s hs hb
  rw [Impl.X448.AArch64.Weak.sqn, WP.seq_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok s n hn') fun t ⟨tc, tg, tm, tr, tw⟩ => ?_
  have kt : VG.Proof.X448.AArch64.Weak.IKeep base s t := VG.Proof.X448.AArch64.Weak.counter_keep tg tm tr tw
  let inv := fun m (u : State) => 1 ≤ m ∧ m ≤ n ∧ VG.Proof.X448.AArch64.Weak.IKeep base s u ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv u.mem base ∧
    u.gpr .x19 = BitVec.ofNat 64 m ∧
    VG.Proof.X448.AArch64.Weak.E u.mem base = Function.update (VG.Proof.X448.AArch64.Weak.E s.mem base) o (Proof.X448.sqn (VG.Proof.X448.AArch64.Weak.E s.mem base o) (n - m))
  refine WP.loop (M := isa) inv ?_ n t ?_
  · intro m u ⟨hm, hm', ku, bu, cu, eu⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [WP.seq_iff]
    refine WP.mono (VG.Proof.X448.AArch64.Weak.mulE (ku.scr hs) bu o o o) fun v ⟨kv, bv, ev⟩ => ?_
    have cv : v.gpr .x19 = BitVec.ofNat 64 (m + 1) := (kv.regs.1 _ (by decide)).trans cu
    refine WP.mono (VG.Proof.X448.AArch64.Weak.decCounter_ok (by omega) cv) fun w ⟨cw, wg, wm, wr, ww, wz⟩ => ?_
    have kw : VG.Proof.X448.AArch64.Weak.IKeep base s w := ku.trans (kv.ikeep.trans (VG.Proof.X448.AArch64.Weak.counter_keep wg wm wr ww))
    have bw : VG.Proof.X448.AArch64.Weak.BoundedEnv w.mem base := wm ▸ bv
    have ew : VG.Proof.X448.AArch64.Weak.E w.mem base = Function.update (VG.Proof.X448.AArch64.Weak.E s.mem base) o (Proof.X448.sqn (VG.Proof.X448.AArch64.Weak.E s.mem base o) (n - m)) := by
      rw [wm, ev, eu, VG.Proof.X448.AArch64.Weak.opMul_update, ← Proof.X448.sqn]
      rw [show (n - (m + 1)).succ = n - m by omega]
    simp only [eval, State.read, BitVec.setWidth_eq, bne, wz]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl ⟨rfl, kw, bw, ew⟩
    · refine Or.inr ⟨?_, m, by omega, hm, by omega, kw, bw, cw, ew⟩
      rw [decide_eq_false (by omega : ¬m = 0)]; rfl
  · refine ⟨hn, by omega, kt, tm ▸ hb, tc, ?_⟩
    rw [tm, Nat.sub_self, Proof.X448.sqn, Function.update_eq_self]

end VG.Proof.X448.AArch64.Weak

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Weak.Inv`. -/
section

/-!
# X448 on AArch64: inversion

Untrusted: everything here is checked by Lean. The addition chain updates
slots 14–21 and leaves the ladder's coordinates available for the final
multiplication and encoding.
-/

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Impl.X448.AArch64.Weak

/-- The field slots after the inversion's addition chain. -/
def invEnv (e : VG.Proof.X448.AArch64.Weak.Env) : VG.Proof.X448.AArch64.Weak.Env :=
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.copy 14 2] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 14 1 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 14 14 2, .copy 15 14] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 15 2 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 15 15 14, .copy 16 15] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 16 4 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 16 16 15, .copy 17 16] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 17 8 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 17 17 16, .copy 18 17] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 18 16 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 18 18 17, .copy 19 18] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 19 32 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 19 19 18, .copy 20 19] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 20 64 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 20 20 19] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 20 64 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 20 20 19] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 20 16 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 20 20 17] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 20 8 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 20 20 16] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 20 4 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 20 20 15] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 20 2 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 20 20 14, .copy 21 20] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 21 1 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 21 21 2] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 21 225 e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 20 2 e
  VG.Proof.X448.AArch64.Weak.applyOps [.mul 20 20 2, .mul 21 21 20] e

theorem invert_spec (base : Addr) : VG.Proof.X448.AArch64.Weak.ISpec base Impl.X448.AArch64.Weak.invert VG.Proof.X448.AArch64.Weak.invEnv := by
  have h : VG.Proof.X448.AArch64.Weak.ISpec base _ _ :=
    (VG.Proof.X448.AArch64.Weak.opsI base [.copy 14 2]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 14 (n := 1) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 14 14 2, .copy 15 14]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 15 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 15 15 14, .copy 16 15]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 16 (n := 4) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 16 16 15, .copy 17 16]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 17 (n := 8) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 17 17 16, .copy 18 17]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 18 (n := 16) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 18 18 17, .copy 19 18]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 19 (n := 32) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 19 19 18, .copy 20 19]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 20 20 19]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 20 20 19]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 20 (n := 16) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 20 20 17]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 20 (n := 8) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 20 20 16]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 20 (n := 4) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 20 20 15]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 20 20 14, .copy 21 20]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 21 (n := 1) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 21 21 2]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 21 (n := 225) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 20 20 2, .mul 21 21 20])
  exact h

theorem invEnv_eval (e : VG.Proof.X448.AArch64.Weak.Env) : VG.Proof.X448.AArch64.Weak.invEnv e 21 = Proof.X448.invert (e 2) := by
  simp only [↓reduceIte, VG.Proof.X448.AArch64.Weak.invEnv, VG.Proof.X448.AArch64.Weak.applyOps, FieldOp.apply, VG.Proof.X448.AArch64.Weak.opMul, VG.Proof.X448.AArch64.Weak.opCopy, VG.Proof.X448.AArch64.Weak.opSqn,
    Function.update_apply]
  rfl

theorem invEnv_x2 (e : VG.Proof.X448.AArch64.Weak.Env) : VG.Proof.X448.AArch64.Weak.invEnv e 1 = e 1 := by
  simp (config := {decide := true}) only [VG.Proof.X448.AArch64.Weak.invEnv, VG.Proof.X448.AArch64.Weak.applyOps, FieldOp.apply, VG.Proof.X448.AArch64.Weak.opMul, VG.Proof.X448.AArch64.Weak.opCopy, VG.Proof.X448.AArch64.Weak.opSqn,
    Function.update_apply, ite_true, ite_false]

theorem invert_ok {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Weak.BoundedEnv s.mem base) :
    WP isa Impl.X448.AArch64.Weak.invert s fun t =>
      VG.Proof.X448.AArch64.Weak.IKeep base s t ∧ VG.Proof.X448.AArch64.Weak.BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = VG.Proof.X448.AArch64.Weak.invEnv (VG.Proof.X448.AArch64.Weak.E s.mem base) :=
  VG.Proof.X448.AArch64.Weak.invert_spec base s hs hb

end VG.Proof.X448.AArch64.Weak

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Weak.Ladder`. -/
section

/-!
# X448 on AArch64: all 448 ladder iterations

Untrusted: everything here is checked by Lean. A decreasing public counter
connects the loop to the specification's descending fold over scalar bits.
-/

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Impl.X448.AArch64.Weak

/-- The ladder's loop, from the counter `n ≥ 1` down to 0. -/
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 448 → VG.Proof.X448.AArch64.Weak.LInv base k u s₀ s n →
      WP isa (.loop VG.Impl.X448.AArch64.Weak.step (.nonzero .x .x19)) s fun s' => VG.Proof.X448.AArch64.Weak.LInv base k u s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := VG.Impl.X448.AArch64.Weak.step) (c := .nonzero .x .x19)
    (Q := fun s' => VG.Proof.X448.AArch64.Weak.LInv base k u s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 448 ∧ VG.Proof.X448.AArch64.Weak.LInv base k u s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (VG.Proof.X448.AArch64.Weak.step_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, State.read, BitVec.setWidth_eq, bne, hz]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

/-- The ladder: the counter set to 448, then the loop. -/
theorem ladder_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t))
    (hi : ∀ s', s'.gpr .x19 = BitVec.ofNat 64 448 → (∀ r, r ≠ .x19 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VG.Proof.X448.AArch64.Weak.LInv base k u s₀ s' 448) :
    WP isa ladder s fun s' => VG.Proof.X448.AArch64.Weak.LInv base k u s₀ s' 0 := by
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok s 448 (by decide))
    fun s' ⟨h1, h2, h3, h4, h5⟩ => VG.Proof.X448.AArch64.Weak.loop_ok hbits 448 s' (by omega) (by omega) (hi s' h1 h2 h3 h4 h5))

end VG.Proof.X448.AArch64.Weak

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Weak.Main`. -/
section

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64 VG.Proof.X448
open VG.Impl.X448.AArch64 (ld st slot SWAP BITS)
open VG.Impl.X448.AArch64.Weak

theorem E_outside {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (i : VG.Proof.X448.AArch64.Weak.Index)
    (hi : slot i.val + 128 ≤ o ∨ o + n ≤ slot i.val) : VG.Proof.X448.AArch64.Weak.E m' base i = VG.Proof.X448.AArch64.Weak.E m base i := by
  simp only [VG.Proof.X448.AArch64.Weak.E, VG.Proof.X448.AArch64.Weak.F]
  exact congrArg toFe (VG.Proof.X448.AArch64.Weak.valN_congr (fun j hj => h.limbs hi
    (by have := i.isLt; simp only [slot]; omega) (by omega : j < 16)))

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa x448 s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.X448.x448AArch64.post s₀ s' := by
  obtain ⟨base, hbase⟩ : ∃ b, s₀.gpr .x3 = b := ⟨_, rfl⟩
  have hn : base.toNat + 8192 ≤ 2 ^ 64 := hbase ▸ hp.sc_fit
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s₀.wr := by rw [hp.wr, ← hbase]; simp
  have hr : ∀ j < 56, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .x2) j) 1 := fun j hj =>
    ⟨pointR s₀, by rw [hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hd : ∀ j < 56, 8192 ≤ ofs base (off (s₀.gpr .x2) j) :=
    fun j hj => far (hbase ▸ hp.point_sc) hj (by decide)
  have kd : ∀ j < 56, 8192 ≤ ofs base (off (s₀.gpr .x1) j) :=
    fun j hj => far (hbase ▸ hp.scalar_sc) hj (by decide)
  rw [x448]
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Weak.setup_ok hbase hw₀ hn rfl hr hd)
    fun s₁ ⟨hs₁, b₁, savedOut₁, k₁, o₁, sv₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ => ?_)
  have kr : ∀ j < 56, InRegions (s₁.rd ++ s₁.wr) (off (s₀.gpr .x1) j) 1 := fun j hj =>
    ⟨scalarR s₀, by rw [k₁.2.1, hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (WP.mono (bits_ok hs₁ (k₁.1 _ (by decide)) kr kd)
    fun s₂ ⟨g₂, rd₂, wr₂, o₂, bits₂⟩ => ?_)
  have k₂ : Keeps bitRegs s₁ s₂ := ⟨g₂, rd₂, wr₂⟩
  refine WP.seq (WP.mono (moveOutput_ok s₂) fun s₃ ⟨out₃, m₃, k₃⟩ => ?_)
  have k03 := k₁.then (k₂.then k₃)
  have hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  have sv₃ : VG.Proof.X448.AArch64.Saved base s₀.gpr s₃.mem := by rw [m₃]; exact sv₁.outside o₂ (by decide)
  have e₃ : ∀ i : VG.Proof.X448.AArch64.Weak.Index, VG.Proof.X448.AArch64.Weak.E s₃.mem base i = VG.Proof.X448.AArch64.Weak.E s₁.mem base i := by
    intro i; rw [m₃]; exact VG.Proof.X448.AArch64.Weak.E_outside o₂ i (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
  have b₃ : VG.Proof.X448.AArch64.Weak.BoundedEnv s₃.mem base := by
    intro i j hj
    rw [m₃, o₂.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) (by omega : j < 16)]
    exact b₁ i j hj
  have kb := bytesAt_outside o₁ kd
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Weak.ladder_ok (s₀ := s₃) (s := s₃)
    (k := Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (s₀.gpr .x1) 56))
    (u := toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (s₀.gpr .x2) 56)))
    (fun t ht => by rw [m₃, bits₂ t ht, kb])
    (fun s' hb hg hm hr hw => ⟨
      ⟨(hg _ (by decide)).trans hs₃.x3, (hg _ (by decide)).trans hs₃.mask, hw ▸ hs₃.wr, hn⟩, hm ▸ b₃,
      ⟨fun r h => hg r (fun e => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
      hb, hm ▸ Outside2.refl _ _ _ _ _ _,
      by rw [hm, e₃ 0, x1₁], by rw [hm, e₃ 1, x2₁]; rfl,
      by rw [hm, e₃ 2, z2₁]; rfl, by rw [hm, e₃ 3, x3₁, x1₁]; rfl,
      by rw [hm, e₃ 4, z3₁]; rfl,
      by rw [hm, m₃, o₂.word (d := SWAP) (by decide) (by decide), sw₁]; rfl⟩)) fun s₄ L => ?_)
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Weak.lastSwap_ok L.scr L.bounded
    (by have := ladderAfter_swap_le
          (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (s₀.gpr .x1) 56))
          (toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (s₀.gpr .x2) 56)))
          (n := 0) (by decide); omega) L.swap) fun s₅ ⟨k₅, b₅, e₅⟩ => ?_)
  have hs₅ := k₅.scr L.scr
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Weak.invert_ok hs₅ b₅) fun s₆ ⟨k₆, b₆, e₆⟩ => ?_)
  have k36 := L.regs.then (k₅.regs.then k₆.regs)
  have sv₆ := ((sv₃.outside2 L.mem (by decide) (by decide)).outside2 k₅.mem (by decide)
    (by decide)).outside2 k₆.mem (by decide) (by decide)
  have out₆ : s₆.gpr .x1 = s₀.gpr .x0 :=
    (k36.1 _ (by decide)).trans (out₃.trans ((g₂ _ (by decide)).trans savedOut₁))
  have k06 := k03.then k36
  have hw₆ : ∀ j < 56, InRegions s₆.wr (off (s₀.gpr .x0) j) 1 := fun j hj =>
    ⟨outR s₀, by rw [k06.2.2, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (VG.Proof.X448.AArch64.Weak.finish_ok (k₆.scr hs₅) b₆ out₆ hw₆
    (fun j hj => far_output (hbase ▸ hp.out_sc) hj) sv₆) fun s' ⟨rb, x20, kf, fm, result⟩ => ?_
  have kall := k06.then kf
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rb
    · exact x20
    all_goals exact kall.1 _ (by decide)
  · change Spec.X448.bytesAt s'.mem (s₀.gpr .x0) 56 = _
    rw [result, x448_eq]
    apply congrArg Spec.X448.encodeUCoordinate
    rw [e₆, VG.Proof.X448.AArch64.Weak.invEnv_x2, VG.Proof.X448.AArch64.Weak.invEnv_eval, e₅]
    simp (config := {decide := true}) only [VG.Proof.X448.AArch64.Weak.opSwap, Function.update_apply, ite_true, ite_false]
    rw [L.x2, L.x3, L.z2, L.z3, VG.Proof.X448.AArch64.Weak.cswap_fst, VG.Proof.X448.AArch64.Weak.cswap_fst]

end VG.Proof.X448.AArch64.Weak

end
