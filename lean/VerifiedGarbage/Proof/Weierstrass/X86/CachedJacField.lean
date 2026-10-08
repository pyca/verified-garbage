import VerifiedGarbage.Impl.Weierstrass.X86.CachedJac
import VerifiedGarbage.Proof.Weierstrass.X86.JacAdd

/-! The cached header and tail compute the same Jacobian addition formula. -/
namespace VG.Proof.Weierstrass.X86.CachedJac
open VG VG.Impl.Weierstrass VG.Impl.Weierstrass.X86

def headN : List FOp :=
  [.mul 0 13 13,.mul 2 11 17,.mul 3 14 0,.mul 4 12 18,
   .mul 5 15 13,.mul 5 5 0,.sub 3 3 2,.sub 5 5 4]

def rename (n : Nat) (S : RcbSlots) (p q o : Pt) (dst i : Nat) : Nat :=
  if i=17 then dst else if i=18 then dst+8*n else rcbσ S p q o i

theorem rename_inj {n : Nat} {S : RcbSlots} {p q o : Pt} {dst : Nat}
    (hA : RcbApart S p q o) (h2 : dst∉rcbW S o) (h3 : dst+8*n∉rcbW S o)
    {w : Nat} (hw : w<9) (y : Nat) (he : rename n S p q o dst y=rename n S p q o dst w) : y=w := by
  have hn17 : w≠17 := by omega
  have hn18 : w≠18 := by omega
  simp only [rename,hn17,hn18,ite_false] at he
  split at he
  · exact False.elim (h2 (he.symm ▸ rcbσ_out S p q o hw))
  · split at he
    · exact False.elim (h3 (he.symm ▸ rcbσ_out S p q o hw))
    · exact hA.inj hw y he

theorem head_eq (n : Nat) (S : RcbSlots) (p q o : Pt) (dst : Nat) :
    Impl.Weierstrass.X86.CachedJac.head n S p q dst=headN.map (FOp.rename (rename n S p q o dst)) := rfl

theorem tail_eq (n : Nat) (S : RcbSlots) (p q o : Pt) (dst : Nat) :
    jacTail S p q o=jacTailN.map (FOp.rename (rename n S p q o dst)) := rfl

theorem rename_out (n : Nat) (S : RcbSlots) (p q o : Pt) (dst i : Nat) (hi : i<9) :
    rename n S p q o dst i∈rcbW S o := by
  simp only [rename,show i≠17 from by omega,show i≠18 from by omega,ite_false]
  exact rcbσ_out S p q o hi

theorem rename_mem (n : Nat) (S : RcbSlots) (p q o : Pt) (dst i : Nat) :
    rename n S p q o dst i∈(rcbW S o++rcbR S p q)++[dst,dst+8*n] := by
  unfold rename
  split
  · simp
  · split
    · simp
    · exact List.mem_append_left _ (rcbσ_mem S p q o i)

theorem slots {n : Nat} {N : List FOp} {S : RcbSlots} {p q o : Pt} {dst : Nat} :
    ∀ op∈N.map (FOp.rename (rename n S p q o dst)),∀ x∈op.out::op.ins,
      x∈(rcbW S o++rcbR S p q)++[dst,dst+8*n] := by
  intro op hop
  obtain ⟨op',_,rfl⟩ := List.mem_map.mp hop
  cases op' <;> simp only [FOp.rename,FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,
    or_false] <;> rintro x (rfl|rfl|rfl) <;> exact rename_mem ..

theorem out {n : Nat} {N : List FOp} (hN : ∀ op∈N,op.out<9) {S : RcbSlots} {p q o : Pt} {dst : Nat}
    {op : FOp} (hop : op∈N.map (FOp.rename (rename n S p q o dst))) : op.out∈rcbW S o := by
  obtain ⟨op',hop',rfl⟩ := List.mem_map.mp hop
  rw [FOp.out_rename]
  exact rename_out n S p q o dst _ (hN op' hop')

theorem head_values {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F)
    (h2 : E 17=E 16*E 16) (h3 : E 18=E 17*E 16) :
    runOps headN E 3=E 14*(E 13*E 13)-E 11*(E 16*E 16) ∧
    runOps headN E 5=E 15*E 13*(E 13*E 13)-E 12*E 16*(E 16*E 16) := by
  simp only [headN,runOps,List.foldl_cons,List.foldl_nil,FOp.run,Function.update_apply]
  simp only [ite_true,h3,h2]
  constructor
  · rfl
  · grind

theorem full_values {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F)
    (h2 : E 17=E 16*E 16) (h3 : E 18=E 17*E 16) :
    (runOps (headN++jacTailN) E 6,runOps (headN++jacTailN) E 7,runOps (headN++jacTailN) E 8)=
      jacAddF (E 11) (E 12) (E 13) (E 14) (E 15) (E 16) := by
  simp only [headN,jacTailN,jacTail,List.cons_append,List.nil_append,
    runOps,List.foldl_cons,List.foldl_nil,FOp.run,Function.update_apply]
  simp only [ite_true,h3,h2,jacAddF,Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

theorem head_run {F : Type _} [Lean.Grind.CommRing F] {n : Nat} {S : RcbSlots} {p q o : Pt} {dst : Nat}
    (hA : RcbApart S p q o) (h2a : dst∉rcbW S o) (h3a : dst+8*n∉rcbW S o)
    (E : Nat → F) (h2 : E dst=E q.z*E q.z) (h3 : E (dst+8*n)=E dst*E q.z) :
    runOps (Impl.Weierstrass.X86.CachedJac.head n S p q dst) E S.t3=
      E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z) ∧
    runOps (Impl.Weierstrass.X86.CachedJac.head n S p q dst) E S.t5=
      E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z) := by
  rw [head_eq n S p q o dst]
  have he := runOps_rename (rename n S p q o dst) headN E
    (fun op hop => rename_inj hA h2a h3a ((show ∀ op∈headN,op.out<9 by decide) op hop))
  have hv := head_values (fun i => E (rename n S p q o dst i)) h2 h3
  exact ⟨(congrFun he 3).trans hv.1,(congrFun he 5).trans hv.2⟩

theorem full_run {F : Type _} [Lean.Grind.CommRing F] {n : Nat} {S : RcbSlots} {p q o : Pt} {dst : Nat}
    (hA : RcbApart S p q o) (h2a : dst∉rcbW S o) (h3a : dst+8*n∉rcbW S o)
    (E : Nat → F) (h2 : E dst=E q.z*E q.z) (h3 : E (dst+8*n)=E dst*E q.z) :
    let ops := Impl.Weierstrass.X86.CachedJac.head n S p q dst++jacTail S p q o
    (runOps ops E o.x,runOps ops E o.y,runOps ops E o.z)=
      jacAddF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) := by
  dsimp only
  rw [head_eq n S p q o dst,tail_eq n S p q o dst,←List.map_append]
  have he := runOps_rename (rename n S p q o dst) (headN++jacTailN) E
    (fun op hop => rename_inj hA h2a h3a
      ((show ∀ op∈headN++jacTailN,op.out<9 by decide) op hop))
  exact (congrArg₂ Prod.mk (congrFun he 6)
    (congrArg₂ Prod.mk (congrFun he 7) (congrFun he 8))).trans
      (full_values (fun i => E (rename n S p q o dst i)) h2 h3)

theorem head_readonly {F : Type _} [Lean.Grind.CommRing F] {n : Nat} {S : RcbSlots} {p q o : Pt}
    {dst : Nat} (hA : RcbApart S p q o) (E : Nat → F) {x : Nat} (hx : x∈rcbR S p q) :
    runOps (Impl.Weierstrass.X86.CachedJac.head n S p q dst) E x=E x := by
  apply runOps_of_not_out
  intro op hop he
  rw [head_eq n S p q o dst] at hop
  exact hA.apart x hx (he ▸ out (show ∀ op∈headN,op.out<9 by decide) hop)

end VG.Proof.Weierstrass.X86.CachedJac
