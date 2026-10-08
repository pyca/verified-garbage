import VerifiedGarbage.Proof.Weierstrass.X86.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.X86.Ladder
import VerifiedGarbage.Proof.Weierstrass.X86.TCombLay
import VerifiedGarbage.Proof.Weierstrass.X86.Rcb3
import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Proof.Weierstrass.Law3

/-!
# The fixed-base comb from tables in memory on x86 (32-bit)

What the comb (`TCombJ.lean`) needs of its tables and constants
(`TCombVals`): the selection's words are the entries' coordinates in
Montgomery form (`tbl_entry`).
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- What the comb needs of its tables `tbl` (affine points, whose Montgomery
forms `tcombWords` are in memory) and constants: `J` tables of `H` entries,
entry `m` of table `j` the point `[(m + 1) 2^(wj)]G`, the start (in
Montgomery form) `[H Σ_{i<J} 2^(wi)]G`, and `R mod p` one. -/
structure TCombVals (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) : Prop where
  len : tbl.length = K.J
  lenH : ∀ j < K.J, (tbl.getD j []).length = K.H
  unit : UnitMod C.p (2 ^ (64 * K.M.n))
  one_lt : K.one < C.p
  one : toM C.p (2 ^ (64 * K.M.n)) K.one = 1
  entry : ∀ j < K.J, ∀ m < K.H, Rep C (Fin.ofNat C.p (combAt tbl j m).1)
    (Fin.ofNat C.p (combAt tbl j m).2) 1 (combPtW C K.w j (m + 1))
  start_lt : K.start.1 < C.p ∧ K.start.2 < C.p
  start : Rep C (toM C.p (2 ^ (64 * K.M.n)) K.start.1) (toM C.p (2 ^ (64 * K.M.n)) K.start.2) 1
    (mul (K.H * geomW K.w K.J) (G C))
  /-- The functions of the field arithmetic, of `n` words modulo `p`. -/
  fn : K.F.k = K.M.n ∧ K.F.m = C.p ∧ Mont.FnOk K.F

/-- `x ∈ l` for the comb's lists, through `toComb`. -/
macro "tcomb_mem" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_append,
  List.mem_singleton, true_or, or_true, combSlots, combWs, combRo, rcbW, rcbR, List.cons_append,
  List.nil_append, TCombCfg.toComb]))

/-- `a ≠ b` (or a conjunction of such, or `a ∉ [b, …]`) from `h`, the conjunction of `¬ x = y`
that a `Nodup` of the slots simplifies to, in either orientation: not `grind`, which takes a tenth
of a second for each. -/
macro "nd_ne " h:ident : tactic => `(tactic| (
  try simp only [ne_eq, List.mem_cons, List.not_mem_nil, or_false, not_or]
  repeat' apply And.intro
  all_goals first
    | simp only [ne_eq, $h:ident, not_false_eq_true]
    | exact Ne.symm (by simp only [ne_eq, $h:ident, not_false_eq_true])))

end VG.Proof.Weierstrass.X86
