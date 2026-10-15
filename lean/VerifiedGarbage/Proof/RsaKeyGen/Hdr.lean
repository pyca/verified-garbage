module

public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Term.TermElabM

/-!
# Words and arrays apart from a list of ranges

The scratch space of key generation is a header of words (`hdrBytes`), then
arrays (`slot w j`). What a step changes is a list of ranges, and a proof that
a header word `k` or the start of an array `j` keeps its value needs it apart
from each of them: `∀ r ∈ L w, 8 k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 k`, or
`∀ r ∈ L w, slot w j + m ≤ r.1 ∨ r.1 + r.2 ≤ slot w j`. Rather than unfold
`L w` and run `omega` on each range for each word, `L_shape` states once that
each range of `L w` is one of a literal list `H` of ranges in the header or lies
within arrays `a` to `a + n` for `(a, n)` of a literal list `A`
(`RangeShape`), and `hdr_of_shape` and `arr_of_shape` give the disjointness by
`decide` on `H` and `A`.

`hdr_disj` proves such a goal from `L_shape`, for the list's function `L`
(and from the shapes of `L₁` and `L₂` for `L₁ ++ L₂`, a literal list being its
own header ranges).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Impl.Bignum (hdrBytes)
open VG.Proof.Bignum (slot)

/-- Each range of `rs` is one of `H` or lies within the arrays `a` to `a + n`,
for some `(a, n)` of `A`. -/
abbrev RangeShape (w : Nat) (H A : List (Nat × Nat)) (rs : List (Nat × Nat)) : Prop :=
  ∀ r ∈ rs, r ∈ H ∨ ∃ p ∈ A, slot w p.1 ≤ r.1 ∧ r.1 + r.2 ≤ slot w (p.1 + p.2)

theorem slot_le_slot {w a b : Nat} (h : a ≤ b) : slot w a ≤ slot w b := by
  unfold slot; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem slot_succ' (w a : Nat) : slot w (a + 1) = slot w a + 8 * (w + 2) := by
  unfold slot; rw [Nat.succ_mul, Nat.add_assoc]

/-- A header word `k` apart from a list of ranges of a shape. -/
theorem hdr_of_shape {w : Nat} {H A rs : List (Nat × Nat)} (hs : RangeShape w H A rs)
    {k : Nat} (hk : 8 * k + 8 ≤ hdrBytes) (hH : ∀ h ∈ H, 8 * k + 8 ≤ h.1 ∨ h.1 + h.2 ≤ 8 * k) :
    ∀ r ∈ rs, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := fun r hr =>
  (hs r hr).elim (hH r) fun ⟨_, _, h, _⟩ =>
    .inl (Nat.le_trans hk (Nat.le_trans (by unfold slot; exact Nat.le_add_right _ _) h))

/-- The first `m` bytes of an array `j` apart from a list of ranges of a shape. -/
theorem arr_of_shape {w : Nat} {H A rs : List (Nat × Nat)} (hs : RangeShape w H A rs)
    {j m : Nat} (hH : ∀ h ∈ H, h.1 + h.2 ≤ hdrBytes) (hA : ∀ p ∈ A, j + 1 ≤ p.1 ∨ p.1 + p.2 ≤ j)
    (hm : m ≤ 8 * (w + 2)) : ∀ r ∈ rs, slot w j + m ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := fun r hr =>
  (hs r hr).elim (fun h => .inr (Nat.le_trans (hH r h) (by unfold slot; exact Nat.le_add_right _ _)))
    fun ⟨p, hp, h1, h2⟩ => (hA p hp).elim
      (fun h => .inl (Nat.le_trans (Nat.add_le_add_left hm _)
        (Nat.le_trans (Nat.le_of_eq (slot_succ' w j).symm) (Nat.le_trans (slot_le_slot h) h1))))
      (fun h => .inr (Nat.le_trans h2 (slot_le_slot h)))

theorem shape_append {w : Nat} {rs rs' H H' A A' : List (Nat × Nat)} (hs : RangeShape w H A rs)
    (hs' : RangeShape w H' A' rs') : RangeShape w (H ++ H') (A ++ A') (rs ++ rs') := fun r hr =>
  (List.mem_append.mp hr).elim
    (fun h => (hs r h).imp (List.mem_append_left H') fun ⟨p, hp, h⟩ => ⟨p, List.mem_append_left A' hp, h⟩)
    (fun h => (hs' r h).imp (List.mem_append_right H) fun ⟨p, hp, h⟩ => ⟨p, List.mem_append_right A hp, h⟩)

/-- A list of ranges is its own header ranges. -/
theorem shape_self (w : Nat) (rs : List (Nat × Nat)) : RangeShape w rs [] rs := fun _ h => .inl h

end VG.Proof.RsaKeyGen

public meta section

namespace VG.Proof.RsaKeyGen

open Lean Elab Tactic Meta

/-- A proof of `RangeShape w H A L` for some `H` and `A`: from `f_shape` for
`L = f a₁ … aₙ`, from the lists' for `L = L₁ ++ L₂`, or `L` itself for a list
literal. -/
partial def rangeShapeOf (L : Expr) : MetaM Expr := do
  let L ← instantiateMVars L
  if L.isAppOfArity ``HAppend.hAppend 6 then
    return ← mkAppM ``shape_append #[← rangeShapeOf (L.getArg! 4), ← rangeShapeOf (L.getArg! 5)]
  if L.isAppOfArity ``List.cons 3 || L.isAppOfArity ``List.nil 1 then
    -- Only closed ranges, which `decide` evaluates.
    if L.hasFVar || L.hasMVar then throwError "hdr_disj: {L} is not a closed list"
    return mkApp2 (mkConst ``shape_self) (← mkFreshExprMVar (mkConst ``Nat)) L
  let some c := L.getAppFn.constName? | throwError "hdr_disj: {L} is not a function's list"
  let shape := c.appendAfter "_shape"
  unless (← getEnv).contains shape do throwError "hdr_disj: no {shape}"
  return mkAppN (← mkConstWithFreshMVarLevels shape) L.getAppArgs

/-- `hdr_disj` proves `∀ r ∈ L, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k` for a header
word `k`, or `∀ r ∈ L, slot w j + m ≤ r.1 ∨ r.1 + r.2 ≤ slot w j` for an array
`j` (and `m ≤ 8 (w + 2)`), from `L`'s shape (`rangeShapeOf`), deciding `k`'s or
`j`'s place against its literal ranges. It fails at once unless `k` or `j` is a
closed term, and if some list of `L` has no shape. -/
elab "hdr_disj" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let .forallE _ _ (.forallE _ mem body _) _ := t | throwError "hdr_disj: not `∀ r ∈ L, …`"
  unless mem.isAppOfArity ``Membership.mem 5 do throwError "hdr_disj: not `∀ r ∈ L, …`"
  unless body.isAppOfArity ``Or 2 && (body.getArg! 0).isAppOfArity ``LE.le 4 do
    throwError "hdr_disj: not `… ≤ r.1 ∨ …`"
  let lo := (body.getArg! 0).getArg! 2
  let closed (e : Expr) := !(e.hasLooseBVars || e.hasFVar || e.hasMVar)
  if closed lo then
    let hs ← Term.exprToSyntax (← rangeShapeOf (mem.getArg! 3))
    evalTactic (← `(tactic| exact VG.Proof.RsaKeyGen.hdr_of_shape $hs (by decide) (by decide)))
  else if lo.isAppOfArity ``HAdd.hAdd 6 && (lo.getArg! 4).isAppOfArity ``VG.Proof.Bignum.slot 2 &&
      closed ((lo.getArg! 4).getArg! 1) then
    let hs ← Term.exprToSyntax (← rangeShapeOf (mem.getArg! 3))
    evalTactic (← `(tactic|
      exact VG.Proof.RsaKeyGen.arr_of_shape $hs (by decide) (by decide) (by omega_using [])))
  else throwError "hdr_disj: not about a header word or an array"

end VG.Proof.RsaKeyGen
