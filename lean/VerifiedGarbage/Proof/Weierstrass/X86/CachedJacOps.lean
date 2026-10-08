import VerifiedGarbage.Proof.Weierstrass.X86.CachedJacField
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! The cached addition's field programs retain the point-operation memory contract. -/
namespace VG.Proof.Weierstrass.X86.CachedJac
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86

theorem head_ok {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hW : WkOk F M m size wk Sl) (hm : UnitMod m (2^(64*M.n)))
    {S : RcbSlots} {p q o : Pt} {dst : Nat} (hA : RcbApart S p q o)
    (h2a : dst∉rcbW S o) (h3a : dst+8*M.n∉rcbW S o)
    (hSl : ∀ x∈(rcbW S o++rcbR S p q)++[dst,dst+8*M.n],Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s)
    (hV : ∀ x∈rcbR S p q++[dst,dst+8*M.n],x∈V)
    (h2 : E dst=E q.z*E q.z) (h3 : E (dst+8*M.n)=E dst*E q.z) :
    WP isa (fprog F (Impl.Weierstrass.X86.CachedJac.head M.n S p q dst)) s fun t =>
      ProgKeep M base wk (rcbW S o) s t ∧
      Inv M base size m Sl (validAfter (Impl.Weierstrass.X86.CachedJac.head M.n S p q dst) V)
        (runOps (Impl.Weierstrass.X86.CachedJac.head M.n S p q dst) E) t ∧
      runOps (Impl.Weierstrass.X86.CachedJac.head M.n S p q dst) E S.t3=
        E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z) ∧
      runOps (Impl.Weierstrass.X86.CachedJac.head M.n S p q dst) E S.t5=
        E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z) := by
  have hr : readsOk (Impl.Weierstrass.X86.CachedJac.head M.n S p q dst) V=true := by
    rw [head_eq M.n S p q o dst]
    exact readsOk_mono (readsOk_rename (rename M.n S p q o dst)
      (show readsOk headN [9,10,11,12,13,14,15,16,17,18]=true by decide)) hV
  have hs : ∀ op∈Impl.Weierstrass.X86.CachedJac.head M.n S p q dst,∀ x∈op.out::op.ins,Sl x := by
    rw [head_eq M.n S p q o dst]
    exact fun op hop x hx => hSl x (slots op hop x hx)
  refine WP.mono (fprog_ok hL hW hm _ hI hs hr) fun t ⟨kt,it⟩ =>
    ⟨kt.mono ?_,it,head_run hA h2a h3a E h2 h3⟩
  intro x hx
  obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
  rw [head_eq M.n S p q o dst] at hop
  exact out (show ∀ op∈headN,op.out<9 by decide) hop

theorem tail_ok {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hW : WkOk F M m size wk Sl) (hm : UnitMod m (2^(64*M.n)))
    {S : RcbSlots} {p q o : Pt} {dst : Nat} (hA : RcbApart S p q o)
    (h2a : dst∉rcbW S o) (h3a : dst+8*M.n∉rcbW S o)
    (hSl : ∀ x∈(rcbW S o++rcbR S p q)++[dst,dst+8*M.n],Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl (validAfter (Impl.Weierstrass.X86.CachedJac.head M.n S p q dst) V)
      (runOps (Impl.Weierstrass.X86.CachedJac.head M.n S p q dst) E) s)
    (hV : ∀ x∈rcbR S p q++[dst,dst+8*M.n],x∈V)
    (h2 : E dst=E q.z*E q.z) (h3 : E (dst+8*M.n)=E dst*E q.z) :
    WP isa (fprog F (jacTail S p q o)) s fun t =>
      ProgKeep M base wk (rcbW S o) s t ∧
      Inv M base size m Sl ([o.x,o.y,o.z]++V)
        (runOps (Impl.Weierstrass.X86.CachedJac.head M.n S p q dst++jacTail S p q o) E) t ∧
      (runOps (Impl.Weierstrass.X86.CachedJac.head M.n S p q dst++jacTail S p q o) E o.x,
       runOps (Impl.Weierstrass.X86.CachedJac.head M.n S p q dst++jacTail S p q o) E o.y,
       runOps (Impl.Weierstrass.X86.CachedJac.head M.n S p q dst++jacTail S p q o) E o.z)=
        jacAddF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) := by
  have hr : readsOk (Impl.Weierstrass.X86.CachedJac.head M.n S p q dst++jacTail S p q o) V=true := by
    rw [head_eq M.n S p q o dst,tail_eq M.n S p q o dst,←List.map_append]
    exact readsOk_mono (readsOk_rename (rename M.n S p q o dst)
      (show readsOk (headN++jacTailN) [9,10,11,12,13,14,15,16,17,18]=true by decide)) hV
  rw [readsOk_append,Bool.and_eq_true] at hr
  have hs : ∀ op∈jacTail S p q o,∀ x∈op.out::op.ins,Sl x := by
    rw [tail_eq M.n S p q o dst]
    exact fun op hop x hx => hSl x (slots op hop x hx)
  refine WP.mono (fprog_ok hL hW hm _ hI hs hr.2) fun t ⟨kt,it⟩ =>
    ⟨kt.mono ?_,?_,full_run hA h2a h3a E h2 h3⟩
  · intro x hx
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
    rw [tail_eq M.n S p q o dst] at hop
    exact out (show ∀ op∈jacTailN,op.out<9 by decide) hop
  · rw [runOps_append]
    apply it.sub
    intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx|hx
    · right
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp [jacTail,FOp.out]
    · exact Or.inl ((mem_validAfter _ _).mpr (Or.inl hx))

end VG.Proof.Weierstrass.X86.CachedJac
