module
public import VerifiedGarbage.Impl.Weierstrass.X86_64.CachedJac
public import VerifiedGarbage.Proof.Weierstrass.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog

import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacField
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAdd

/-! The cached addition's field programs retain the point-operation memory contract. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.CachedJac
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem head_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n)))
    {S : RcbSlots} {p q o : Pt} {dst : Nat} (hA : RcbApart S p q o)
    (h2a : dst∉rcbW S o) (h3a : dst+8*M.n∉rcbW S o)
    (hSl : ∀ x∈(rcbW S o++rcbR S p q)++[dst,dst+8*M.n],Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s)
    (hV : ∀ x∈rcbR S p q++[dst,dst+8*M.n],x∈V)
    (h2 : E dst=E q.z*E q.z) (h3 : E (dst+8*M.n)=E dst*E q.z) :
    WP isa (ForwardField.programB M (Impl.Weierstrass.X86_64.CachedJac.headZ M.n S p q o dst)).inline s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size m Sl (validAfter (Impl.Weierstrass.X86_64.CachedJac.headZ M.n S p q o dst) V)
        (runOps (Impl.Weierstrass.X86_64.CachedJac.headZ M.n S p q o dst) E) t ∧
      runOps (Impl.Weierstrass.X86_64.CachedJac.headZ M.n S p q o dst) E S.t3=
        E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z) ∧
      runOps (Impl.Weierstrass.X86_64.CachedJac.headZ M.n S p q o dst) E S.t5=
        E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z) := by
  have hr : readsOk (Impl.Weierstrass.X86_64.CachedJac.headZ M.n S p q o dst) V=true := by
    rw [headZ_eq M.n S p q o dst]
    exact readsOk_mono (readsOk_rename (rename M.n S p q o dst)
      (show readsOk headZN [9,10,11,12,13,14,15,16,17,18]=true by decide)) hV
  have hs : ∀ op∈Impl.Weierstrass.X86_64.CachedJac.headZ M.n S p q o dst,∀ x∈op.out::op.ins,Sl x := by
    rw [headZ_eq M.n S p q o dst]
    exact fun op hop x hx => hSl x (slots op hop x hx)
  refine WP.mono (ForwardField.programB_ok hL hm _ hI hs hr) fun t ⟨kt,it⟩ =>
    ⟨kt.mono ?_,it,head_run hA h2a h3a E h2 h3⟩
  intro x hx
  obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
  rw [headZ_eq M.n S p q o dst] at hop
  exact out (show ∀ op∈headZN,op.out<9 by decide) hop

end VG.Proof.Weierstrass.X86_64.CachedJac
