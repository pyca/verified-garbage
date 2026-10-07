import VerifiedGarbage.Proof.Weierstrass.AArch64.NafEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoadTiming

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

theorem nafPublicFields_ok {K : WinCfg} {base : Addr} {size : Nat} {b : BitVec 8} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hn : K.M.n=4) (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    {V : List Nat} {E : Nat → Spec.Weierstrass.Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (h2 : s.gpr .x2 = b.setWidth 64) (ha : 1 ≤ (nafMagnitude b+1)/2) (ht : K.tbl < 4096)
    (hD : ∀ x ∈ [K.E.x,K.E.y,K.E.z], Sl x)
    (hT : ∀ x ∈ [(Jacobian.tablePt K ((nafMagnitude b+1)/2)).x,(Jacobian.tablePt K ((nafMagnitude b+1)/2)).y,(Jacobian.tablePt K ((nafMagnitude b+1)/2)).z], x ∈ V)
    (hap : K.E.x+96 ≤ K.tbl+96*((nafMagnitude b+1)/2-1) ∨ K.tbl+96*((nafMagnitude b+1)/2-1)+96 ≤ K.E.x)
 :
    WP isa (.block (Naf.digitIndex ++ Jacobian.publicEntry K)) s fun t =>
      ProgKeep K.M base [K.E.x,K.E.y,K.E.z] s t ∧
      Inv K.M base size C.p Sl ([K.E.x,K.E.y,K.E.z]++V) (tmv C K.M.n base t) t ∧
      (tmv C K.M.n base t K.E.x,tmv C K.M.n base t K.E.y,tmv C K.M.n base t K.E.z) =
        (E (Jacobian.tablePt K ((nafMagnitude b+1)/2)).x,E (Jacobian.tablePt K ((nafMagnitude b+1)/2)).y,E (Jacobian.tablePt K ((nafMagnitude b+1)/2)).z) := by
  rw [WP.block_append_iff]
  refine WP.mono (nafIndex_ok h2) fun u ⟨u2,ku⟩ => ?_
  refine WP.mono (jacPublicFields_ok hL hAl hn hy hz (hI.of_keeps ku (by decide)) u2 ha ht hD hT hap)
    fun t ⟨kt,it,vt⟩ => ⟨?_,it,vt⟩
  exact (keeps_prog ku (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [clob])).trans kt

theorem nafPublic_relCT {K : WinCfg} {base : Addr} {size : Nat} {b : BitVec 8} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hn : K.M.n=4) (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    {V : List Nat} {E : Nat → Fe C}
    (hD : ∀ x∈jacCoords K.E, Sl x)
    (hT : ∀ x∈jacCoords (Jacobian.tablePt K ((nafMagnitude b+1)/2)), x∈V)
    (hap : K.E.x+96≤K.tbl+96*((nafMagnitude b+1)/2-1) ∨ K.tbl+96*((nafMagnitude b+1)/2-1)+96≤K.E.x)
    (ha : 1 ≤ (nafMagnitude b+1)/2) (ht : K.tbl < 4096)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x2]))
      (.block (Naf.digitIndex ++ Jacobian.publicEntry K))) :
    RelCT isa (fun s t => FieldPair K.M base size C.p Sl V E s t ∧
      s.gpr .x2=b.setWidth 64 ∧ t.gpr .x2=b.setWidth 64)
      (.block (Naf.digitIndex ++ Jacobian.publicEntry K))
      (fun s t => ∃ E', FieldPair K.M base size C.p Sl (jacCoords K.E++V) E' s t) := by
  let q := Jacobian.tablePt K ((nafMagnitude b+1)/2)
  let F := fun x => if x=K.E.x then E q.x else if x=K.E.y then E q.y else E q.z
  apply fieldWrite_relCT (F:=F) hL hct
  · intro s t hp ps pt
    refine ⟨hp.sp,fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
    · exact ps.trans pt.symm
  · exact hD
  · intro x hx; exact List.mem_append.mp hx
  · intro s hi hp
    refine WP.mono (nafPublicFields_ok hL hAl hn hy hz hi hp ha ht hD hT hap)
      fun t ⟨hk,it,ht⟩ => ⟨_,hk,it,?_⟩
    intro x _ hx
    simp only [Prod.mk.injEq] at ht
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simpa only [F,ite_true] using ht.1
    · simpa only [F,show K.E.y ≠ K.E.x by omega,ite_false,ite_true] using ht.2.1
    · simpa only [F,show K.E.z ≠ K.E.x by omega,show K.E.z ≠ K.E.y by omega,ite_false] using ht.2.2

end VG.Proof.Weierstrass.AArch64
