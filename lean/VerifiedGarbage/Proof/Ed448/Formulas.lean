import VerifiedGarbage.Impl.Ed448.Formulas
import VerifiedGarbage.Proof.Ed448.Ref
import Mathlib.Logic.Function.Basic

/-!
# Ed448: the point formulas' field programs, evaluated

Target-independent and light. A field program (`Impl/Ed448/Formulas.lean`)
evaluates on twenty-two field-element slots (`evalOps`): each operation
replaces its destination. A target's proof shows that its code for each
operation updates its slots so; then `doubleOps` doubles the point in slots
0–2 (`double`) and `addOps` adds the point in slots 8–10 to it, into slots
3–5 (`addWith`, the specification's `pointAdd` with `d` the value of slot
11), and each leaves the other slots it does not write as they were.
-/

namespace VG.Proof.Ed448

open VG.Impl.Ed448 (FOp doubleOps addOps)
open Spec.X448 (Fe)

/-- A slot by its number (below 22 in every program here). -/
def idx (n : Nat) : Fin 22 := ⟨n % 22, Nat.mod_lt _ (by decide)⟩

/-- Every slot of the operation is below 22. -/
def fopValid : FOp → Prop
  | .mul o a b | .add o a b | .sub o a b => o < 22 ∧ a < 22 ∧ b < 22
  | .sqr o a => o < 22 ∧ a < 22

instance (op : FOp) : Decidable (fopValid op) := by cases op <;> unfold fopValid <;> infer_instance

/-- The slots after an operation. -/
def evalOp : FOp → (Fin 22 → Fe) → Fin 22 → Fe
  | .mul o a b, e => Function.update e (idx o) (e (idx a) * e (idx b))
  | .sqr o a, e => Function.update e (idx o) (e (idx a) * e (idx a))
  | .add o a b, e => Function.update e (idx o) (e (idx a) + e (idx b))
  | .sub o a b, e => Function.update e (idx o) (e (idx a) - e (idx b))

def evalOps (ops : List FOp) (e : Fin 22 → Fe) : Fin 22 → Fe := ops.foldl (fun e op => evalOp op e) e

/-- The point in slots `i`, `j`, `k`. -/
def pt (e : Fin 22 → Fe) (i j k : Fin 22) : Spec.Ed448.Point := ⟨e i, e j, e k⟩

/-- The specification's addition, with `d` a parameter. -/
def addWith (dd : Fe) (p q : Spec.Ed448.Point) : Spec.Ed448.Point :=
  let a := p.Z * q.Z
  let b := a * a
  let c := p.X * q.X
  let d' := p.Y * q.Y
  let e := dd * c * d'
  let f := b - e
  let g := b + e
  let h := (p.X + p.Y) * (q.X + q.Y)
  ⟨a * f * (h - c - d'), a * g * (d' - c), f * g⟩

theorem addWith_d (p q : Spec.Ed448.Point) : addWith Spec.Ed448.d p q = Spec.Ed448.pointAdd p q := rfl

theorem doubleOps_valid : ∀ op ∈ doubleOps, fopValid op := by decide
theorem addOps_valid : ∀ op ∈ addOps, fopValid op := by decide

theorem doubleOps_eval (e : Fin 22 → Fe) :
    pt (evalOps doubleOps e) 0 1 2 = double (pt e 0 1 2) := rfl

theorem addOps_eval (e : Fin 22 → Fe) :
    pt (evalOps addOps e) 3 4 5 = addWith (e 11) (pt e 0 1 2) (pt e 8 9 10) := rfl

/-- The slot an operation writes. -/
def fopDest : FOp → Nat
  | .mul o _ _ | .sqr o _ | .add o _ _ | .sub o _ _ => o

theorem evalOps_keep (ops : List FOp) (e : Fin 22 → Fe) (i : Fin 22)
    (hi : ∀ op ∈ ops, fopDest op % 22 ≠ i.val) : evalOps ops e i = e i := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih =>
    change evalOps ops (evalOp op e) i = e i
    rw [ih _ fun o h => hi o (List.mem_cons_of_mem _ h)]
    have h := hi op List.mem_cons_self
    have hne : i ≠ idx (fopDest op) := fun h' => h (by rw [h']; rfl)
    cases op <;> simp only [evalOp] <;> exact Function.update_of_ne hne _ _

theorem doubleOps_keep (e : Fin 22 → Fe) (i : Fin 22) (hi : 3 ≤ i.val ∧ i.val < 12 ∨ i.val = 20 ∨ i.val = 21) :
    evalOps doubleOps e i = e i :=
  evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ doubleOps, fopDest op < 3 ∨ (12 ≤ fopDest op ∧ fopDest op < 20) := by decide
    have := this op hop
    omega

theorem addOps_keep (e : Fin 22 → Fe) (i : Fin 22) (hi : i.val < 3 ∨ (6 ≤ i.val ∧ i.val < 12) ∨ i.val = 21) :
    evalOps addOps e i = e i :=
  evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ addOps, (3 ≤ fopDest op ∧ fopDest op < 6) ∨ (12 ≤ fopDest op ∧ fopDest op < 21) := by decide
    have := this op hop
    omega

end VG.Proof.Ed448
