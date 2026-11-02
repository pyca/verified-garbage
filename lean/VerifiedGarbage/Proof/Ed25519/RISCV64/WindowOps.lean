module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldProg
public import VerifiedGarbage.Proof.Ed25519.BaseTable
public import VerifiedGarbage.Proof.Ed25519.DblPoint
public import VerifiedGarbage.Impl.Ed25519.RISCV64.VerifyWindow
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Defs

/-!
# The windows' field programs on RISC-V

As on AArch64 (`Proof/Ed25519/AArch64/WindowStep.lean`): the doubling's
program is `dblPoint` (`dblOps_eval`), the cached addition's is the
specification's `pointAdd` of the point and the one cached (`ring`), and
`cacheOps` is `cache` of the point saved in slots 17–20. Each keeps the
slots it does not write: the doubling and the addition slots 16 and up, and
the doubling the cached point in slots 4–7.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.Impl.Ed25519.RISCV64
open Fin.CommRing

theorem dblOps_eval (e : Env) : point (evalOps dblOps e) 0 1 2 3 = dblPoint (point e 0 1 2 3) := rfl

/-- Slots `ops` does not write keep their elements. -/
theorem evalOps_keep (ops : List FieldOp) (e : Env) (i : Slot)
    (h : ∀ op ∈ ops, match op with
      | .copy o _ | .const o _ | .mul o _ _ | .mulc o _ _ | .add o _ _ | .sub o _ _ => o ≠ i) :
    evalOps ops e i = e i := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih =>
    simp only [evalOps, List.foldl_cons] at ih ⊢
    rw [ih _ fun op' h' => h op' (List.mem_cons_of_mem _ h')]
    have hop := h op List.mem_cons_self
    cases op <;> simp only [evalOp] at hop ⊢ <;> exact Function.update_of_ne (Ne.symm hop) _ _

theorem dblOps_keep (e : Env) (i : Slot) (hi : 4 ≤ i.val ∧ i.val < 8 ∨ 15 ≤ i.val) :
    evalOps dblOps e i = e i :=
  evalOps_keep _ e i fun op hop => by
    simp only [dblOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact fun h => by subst h; revert hi; decide

def addCachedResult (e : Env) : Spec.Ed25519.Point :=
  let a := (e 1 - e 0) * e 4
  let b := (e 1 + e 0) * e 5
  let c := e 3 * e 6
  let dd := e 2 * e 7
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAddCached_formula (e : Env) :
    point (evalOps pointAddCachedOps e) 0 1 2 3 = addCachedResult e := rfl

theorem pointAddCached_eval (e : Env) (q : Spec.Ed25519.Point) (hq : point e 4 5 6 7 = cache q) :
    point (evalOps pointAddCachedOps e) 0 1 2 3 = Spec.Ed25519.pointAdd (point e 0 1 2 3) q := by
  have h4 : e 4 = q.Y - q.X := congrArg Spec.Ed25519.Point.X hq
  have h5 : e 5 = q.Y + q.X := congrArg Spec.Ed25519.Point.Y hq
  have h6 : e 6 = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z hq
  have h7 : e 7 = q.Z * 2 := congrArg Spec.Ed25519.Point.T hq
  rw [pointAddCached_formula]
  simp only [addCachedResult, point, Spec.Ed25519.pointAdd, h4, h5, h6, h7]
  congr 1 <;> ring

theorem pointAddCached_keep (e : Env) (i : Slot) (hi : 4 ≤ i.val ∧ i.val < 8 ∨ 16 ≤ i.val) :
    evalOps pointAddCachedOps e i = e i :=
  evalOps_keep _ e i fun op hop => by
    simp only [pointAddCachedOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact fun h => by subst h; revert hi; decide

theorem cacheOps_keep (e : Env) (i : Slot) (hi : 4 ≤ i.val ∧ i.val < 8 ∨ i.val = 16 ∨ i.val = 21) :
    evalOps (savePointOps ++ cacheOps) e i = e i :=
  evalOps_keep _ e i fun op hop => by
    simp only [savePointOps, cacheOps, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact fun h => by subst h; revert hi; decide

/-- The point saved in slots 17–20, then cached into slots 0–3. -/
theorem cacheOps_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps (savePointOps ++ cacheOps) e) 0 1 2 3 = cache (point e 0 1 2 3) ∧
      point (evalOps (savePointOps ++ cacheOps) e) 17 18 19 20 = point e 0 1 2 3 := by
  refine ⟨?_, rfl⟩
  simp only [evalOps, savePointOps, cacheOps, List.cons_append, List.nil_append, List.foldl_cons,
    List.foldl_nil, evalOp, point, cache]
  simp [hd]
  constructor <;> ring

end VG.Proof.Ed25519.RISCV64
