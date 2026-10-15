module

public import VerifiedGarbage.Proof.Bignum.Layout
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Term.TermElabM

/-!
# Header words apart from a list of ranges

The scratch space of key generation is a header of words (`hdrBytes`), then
arrays. What a step changes is a list of ranges, and a proof that a header
word `k` keeps its value needs `k` apart from each of them:
`∀ r ∈ L w, 8 k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 k`. Rather than unfold `L w` and
run `omega` on each range for each word, `L_shape` states once that each
range of `L w` is past the header or one of a literal list of ranges in it,
and `hdr_of_shape` gives the disjointness of any word from it by `decide`.

`hdr_disj` proves such a goal from `L_shape`, for the list's function `L`
(and from the shapes of `L₁` and `L₂` for `L₁ ++ L₂`, a literal list being its
own header ranges).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Impl.Bignum (hdrBytes)

/-- A header word `k` apart from each range of a list whose ranges are past
the header or in `H`. -/
theorem hdr_of_shape {rs : List (Nat × Nat)} (H : List (Nat × Nat)) (hs : ∀ r ∈ rs, hdrBytes ≤ r.1 ∨ r ∈ H)
    {k : Nat} (hk : 8 * k + 8 ≤ hdrBytes) (hH : ∀ h ∈ H, 8 * k + 8 ≤ h.1 ∨ h.1 + h.2 ≤ 8 * k) :
    ∀ r ∈ rs, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := fun r hr =>
  (hs r hr).elim (fun h => .inl (Nat.le_trans hk h)) (hH r)

theorem shape_mono {rs : List (Nat × Nat)} {H H' : List (Nat × Nat)} (hs : ∀ r ∈ rs, hdrBytes ≤ r.1 ∨ r ∈ H)
    (hH : ∀ h ∈ H, h ∈ H') : ∀ r ∈ rs, hdrBytes ≤ r.1 ∨ r ∈ H' := fun r hr =>
  (hs r hr).imp_right (hH r)

theorem shape_append {rs rs' : List (Nat × Nat)} {H : List (Nat × Nat)} (hs : ∀ r ∈ rs, hdrBytes ≤ r.1 ∨ r ∈ H)
    (hs' : ∀ r ∈ rs', hdrBytes ≤ r.1 ∨ r ∈ H) : ∀ r ∈ rs ++ rs', hdrBytes ≤ r.1 ∨ r ∈ H := fun r hr =>
  (List.mem_append.mp hr).elim (hs r) (hs' r)

theorem shape_append' {rs rs' H H' : List (Nat × Nat)} (hs : ∀ r ∈ rs, hdrBytes ≤ r.1 ∨ r ∈ H)
    (hs' : ∀ r ∈ rs', hdrBytes ≤ r.1 ∨ r ∈ H') : ∀ r ∈ rs ++ rs', hdrBytes ≤ r.1 ∨ r ∈ H ++ H' := fun r hr =>
  (List.mem_append.mp hr).elim (fun h => (hs r h).imp_right (List.mem_append_left H'))
    (fun h => (hs' r h).imp_right (List.mem_append_right H))

/-- A list of ranges is its own header ranges. -/
theorem shape_self (rs : List (Nat × Nat)) : ∀ r ∈ rs, hdrBytes ≤ r.1 ∨ r ∈ rs := fun _ h => .inr h

end VG.Proof.RsaKeyGen

public meta section

namespace VG.Proof.RsaKeyGen

open Lean Elab Tactic Meta

/-- A proof of `∀ r ∈ L, hdrBytes ≤ r.1 ∨ r ∈ H` for some `H`: from `f_shape` for `L = f a₁ … aₙ`,
from the lists' for `L = L₁ ++ L₂`, or `L` itself for a list literal. -/
partial def hdrShapeOf (L : Expr) : MetaM Expr := do
  let L ← instantiateMVars L
  if L.isAppOfArity ``HAppend.hAppend 6 then
    return ← mkAppM ``shape_append' #[← hdrShapeOf (L.getArg! 4), ← hdrShapeOf (L.getArg! 5)]
  if L.isAppOfArity ``List.cons 3 || L.isAppOfArity ``List.nil 1 then
    return mkApp (mkConst ``shape_self) L
  let some c := L.getAppFn.constName? | throwError "hdr_disj: {L} is not a function's list"
  let shape := c.appendAfter "_shape"
  unless (← getEnv).contains shape do throwError "hdr_disj: no {shape}"
  return mkAppN (← mkConstWithFreshMVarLevels shape) L.getAppArgs

/-- `hdr_disj` proves `∀ r ∈ L, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k` for a header
word `k` from `L`'s shape (`hdrShapeOf`), deciding `k`'s place against its header
ranges. It fails if some list of `L` has no shape. -/
elab "hdr_disj" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let .forallE _ _ (.forallE _ mem body _) _ := t | throwError "hdr_disj: not `∀ r ∈ L, …`"
  unless mem.isAppOfArity ``Membership.mem 5 do throwError "hdr_disj: not `∀ r ∈ L, …`"
  -- Fail at once unless the word is a closed term: `8 * k + 8 ≤ r.1 ∨ …`.
  unless body.isAppOfArity ``Or 2 && (body.getArg! 0).isAppOfArity ``LE.le 4 do
    throwError "hdr_disj: not `… ≤ r.1 ∨ …`"
  let lo := (body.getArg! 0).getArg! 2
  if lo.hasLooseBVars || lo.hasFVar || lo.hasMVar then throwError "hdr_disj: not a header word"
  let hs ← Term.exprToSyntax (← hdrShapeOf (mem.getArg! 3))
  evalTactic (← `(tactic| exact VG.Proof.RsaKeyGen.hdr_of_shape _ $hs (by decide) (by decide)))

end VG.Proof.RsaKeyGen
