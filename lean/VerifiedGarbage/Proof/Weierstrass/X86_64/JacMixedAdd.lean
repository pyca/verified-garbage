module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacDouble
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Block
import Batteries.Logic

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- The two copied coordinates are initialized before the mixed formula reads them. -/
theorem jacMixedInit_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    {S : RcbSlots} {p q o : Pt} (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (.block (copy M.n S.t2 p.x ++ copy M.n S.t4 p.y)) s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size m Sl (S.t4::S.t2::V) (jacMixedInit S p E) t := by
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL hI (hSl S.t2 (by simp [rcbW]))
    (hV p.x (by simp [rcbR]))) fun a ⟨ka,ia⟩ => ?_
  refine WP.mono (copyField_ok hL ia (hSl S.t4 (by simp [rcbW]))
    (List.mem_cons_of_mem _ (hV p.y (by simp [rcbR])))) fun t ⟨kt,it⟩ =>
    ⟨(progKeep_of_op ka (by simp [rcbW])).trans (progKeep_of_op kt (by simp [rcbW])),it⟩

/-- Read-only coordinates survive the two initialization copies and header. -/
theorem jacMixedHead_readonly {F : Type _} [Lean.Grind.CommRing F]
    {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o) (E : Nat → F)
    {x : Nat} (hx : x ∈ rcbR S p q) :
    runOps (jacMixedHead S p q) (jacMixedInit S p E) x = E x := by
  have hn2 : x≠S.t2 := fun he => hA.apart x hx (by rw [he]; simp [rcbW])
  have hn4 : x≠S.t4 := fun he => hA.apart x hx (by rw [he]; simp [rcbW])
  rw [runOps_of_not_out]
  · simp only [jacMixedInit,Function.update_of_ne hn2,Function.update_of_ne hn4]
  · intro op hop he
    have ho : op.out ∈ rcbW S o := by
      rw [jacMixedHead_eq S p q o] at hop
      obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hop
      rw [FOp.out_rename]
      exact rcbσ_out S p q o ((show ∀ n ∈ jacMixedHeadN, n.out<9 by decide) n hn)
    exact hA.apart x hx (he ▸ ho)

end VG.Proof.Weierstrass.X86_64
