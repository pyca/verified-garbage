import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedField
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64

def inputs : List Nat := rcbR K.S K.R K.E ++ [5400,5432]
def slots : List Nat := rcbW K.S K.D ++ inputs

def ops : CachedJac.Ops where
  head := VG.Impl.P256.VerifyArithmetic.program K.M head
  tail := VG.Impl.P256.VerifyArithmetic.program K.M tail
  double := VG.Impl.P256.VerifyDouble.double K.M K.S K.R K.D

theorem slots_head : ∀ op∈head,∀ x∈op.out::op.ins,x∈slots := by decide +kernel
theorem slots_tail : ∀ op∈tail,∀ x∈op.out::op.ins,x∈slots := by decide +kernel
theorem writes_head : ∀ op∈head,op.out∈rcbW K.S K.D := by decide +kernel
theorem writes_tail : ∀ op∈tail,op.out∈rcbW K.S K.D := by decide +kernel
theorem out_tail : ∀ x∈[K.D.x,K.D.y,K.D.z],x∈tail.map FOp.out := by decide +kernel
theorem reads_head : readsOk head inputs=true := by decide +kernel
theorem reads_full : readsOk (head++tail) inputs=true := by decide +kernel

theorem head_readonly {F : Type} [Lean.Grind.CommRing F] (E : Nat → F)
    {x : Nat} (hx : x∈inputs) : runOps head E x=E x := by
  apply runOps_of_not_out
  have h : ∀ op∈head,∀ x∈inputs,op.out≠x := by decide +kernel
  exact fun op hop => h op hop x hx

theorem head_ok {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hm : UnitMod m (2^(64*K.M.n))) (hsize : 8192≤size)
    (hSl : ∀ x∈slots,Sl x) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv K.M base size m Sl V E s) (hV : ∀ x∈inputs,x∈V)
    (h2 : E 5400=E K.E.z*E K.E.z) (h3 : E 5432=E K.E.z*(E K.E.z*E K.E.z)) :
    WP isa ops.head s fun t =>
      ProgKeep K.M base (rcbW K.S K.D) s t ∧
      Inv K.M base size m Sl (validAfter head V) (runOps head E) t ∧
      runOps head E K.S.t3=E K.E.x*(E K.R.z*E K.R.z)-E K.R.x*(E K.E.z*E K.E.z) ∧
      runOps head E K.S.t5=E K.E.y*E K.R.z*(E K.R.z*E K.R.z)-E K.R.y*E K.E.z*(E K.E.z*E K.E.z) := by
  dsimp only [ops]
  refine WP.mono (Forward.Arithmetic.field_ok Forward.Arithmetic.cases (M:=K.M) hL hAl hm hsize head hI
    (fun op hop x hx => hSl x (slots_head op hop x hx)) (fun _ _ => Low.small (by decide) _) (readsOk_mono reads_head hV))
    fun t ⟨hk,hi⟩ => ⟨hk.mono ?_,hi,head_values E h2 h3⟩
  intro x hx
  obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
  exact writes_head op hop

theorem tail_ok {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hm : UnitMod m (2^(64*K.M.n))) (hsize : 8192≤size)
    (hSl : ∀ x∈slots,Sl x) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv K.M base size m Sl (validAfter head V) (runOps head E) s)
    (hV : ∀ x∈inputs,x∈V)
    (h2 : E 5400=E K.E.z*E K.E.z) (h3 : E 5432=E K.E.z*(E K.E.z*E K.E.z)) :
    WP isa ops.tail s fun t =>
      ProgKeep K.M base (rcbW K.S K.D) s t ∧
      Inv K.M base size m Sl ([K.D.x,K.D.y,K.D.z]++V) (runOps (head++tail) E) t ∧
      (runOps (head++tail) E K.D.x,runOps (head++tail) E K.D.y,runOps (head++tail) E K.D.z)=
        jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) (E K.E.z) := by
  have hr := readsOk_mono reads_full hV
  rw [readsOk_append,Bool.and_eq_true] at hr
  dsimp only [ops]
  refine WP.mono (Forward.Arithmetic.field_ok Forward.Arithmetic.cases (M:=K.M) hL hAl hm hsize tail hI
    (fun op hop x hx => hSl x (slots_tail op hop x hx)) (fun _ _ => Low.small (by decide) _) hr.2)
    fun t ⟨hk,hi⟩ => ⟨hk.mono ?_,?_,full_values E h2 h3⟩
  · intro x hx
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
    exact writes_tail op hop
  · rw [runOps_append]
    apply hi.sub
    intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (out_tail x hx)
    · exact Or.inl ((mem_validAfter _ _).mpr (Or.inl hx))

end VG.Proof.Weierstrass.AArch64.CachedField
