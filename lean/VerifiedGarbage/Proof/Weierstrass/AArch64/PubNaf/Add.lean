module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# Jacobian addition and doubling whose products may be calls

`ofN_partialB_ok` is `ofN_partial_ok` for products that are calls of a
function (the slots of the formulas below the function's working space,
`Low`). For a modulus other than P-256's measured layouts, the exceptional
doubling is `dblJMul` (`VerifyDouble.double`, `verifyDouble_eq`). `dblB_ok`
is a doubling `dblJ` or `dblJMul`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Impl.Weierstrass VG.Proof.Mont.AArch64 VG.Proof.Mont
open Spec.Weierstrass

/-- Only four-word moduli take P-256's forwarded doubling. -/
theorem verifyDouble_eq {m : Mod} (hn : m.n ≠ 4) (S : RcbSlots) (p o : Pt) :
    VG.Impl.P256.VerifyDouble.double m S p o = fprogB m (dblJMul S p o) := by
  unfold VG.Impl.P256.VerifyDouble.double
  refine ite_eq_right_iff.mpr fun h => absurd ?_ hn
  obtain ⟨rfl, -⟩ := h
  rfl

/-- `ofN_partial_ok` for products that may be calls. -/
theorem ofN_partialB_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {N : List FOp}
    (hN : ∀ op ∈ N, op.out < 9) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    (hLow : Low M (rcbW S o ++ rcbR S p q))
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s)
    (hR : readsOk (ofN N S p q o) V = true) :
    WP isa (fprogB M (ofN N S p q o)) s fun s' =>
      ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl (validAfter (ofN N S p q o) V)
        (runOps (ofN N S p q o) E) s' ∧
      ∀ i, runOps (ofN N S p q o) E (rcbσ S p q o i) =
        runOps N (fun j => E (rcbσ S p q o j)) i := by
  refine WP.mono (fprogB_ok hL hAl hm _ hI
    (fun op hop x hx => hSl x (ofN_slots op hop x hx))
    (fun op hop => hLow.mono (ofN_slots op hop)) hR) fun s' ⟨hk, hi⟩ => ⟨hk.mono ?_, hi, ?_⟩
  · intro w hw
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    obtain ⟨op', hop', rfl⟩ := List.mem_map.mp hop
    rw [FOp.out_rename]
    exact rcbσ_out S p q o (hN op' hop')
  · intro i
    exact congrFun (runOps_rename (rcbσ S p q o) N E
      (fun op hop => hA.inj (hN op hop))) i

/-- A Jacobian doubling, `dblJMul` (`direct`) or `dblJ`, whose products may be calls. -/
theorem dblB_ok (direct : Bool) {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod C.p (2^(64*M.n))) (hC : Law C) (ha : AM3 C)
    {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p p, Sl x) (hLow : Low M (rcbW S o ++ rcbR S p p))
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x ∈ rcbR S p p, x ∈ V) {P : Point C}
    (hP : onCurve C P = true) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprogB M (if direct then dblJMul S p o else dblJ S p o)) s
      (JacPost M S base size C Sl V o (Spec.Weierstrass.add P P) s) := by
  have he : (if direct then dblJMul S p o else dblJ S p o) = ofN (dblJChoiceN direct) S p p o := by
    cases direct
    · exact dblJChoice_eq false S p o
    · exact dblJChoice_eq true S p o
  rw [he]
  refine WP.mono (ofN_ok hL hAl hm (dblJChoiceN_ok direct) hA hSl hLow hI hV)
    fun t ⟨hk, hi, hv⟩ => ⟨_, hk, hi, ?_⟩
  exact InvJ.dbl' hC ha hP hJ (hv.trans (dblJChoiceN_run direct _))

end VG.Proof.Weierstrass.AArch64
