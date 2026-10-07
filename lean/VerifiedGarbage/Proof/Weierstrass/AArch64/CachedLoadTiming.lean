import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedEntryLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoadTiming

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

abbrev lookupCode := Naf.digitIndex++CachedJac.load++Jacobian.publicEntry K

theorem lookupFields_ok {base : Addr} {size : Nat} {b : BitVec 8} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hsize : 6512≤size)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hi : Inv K.M base size C.p Sl V E s)
    (h2 : s.gpr .x2=b.setWidth 64)
    (ha : 1≤(nafMagnitude b+1)/2) (ha8 : (nafMagnitude b+1)/2≤8)
    (hD : ∀ x∈entryWrites,Sl x)
    (hT : ∀ x∈[(Jacobian.tablePt K ((nafMagnitude b+1)/2)).x,
      (Jacobian.tablePt K ((nafMagnitude b+1)/2)).y,(Jacobian.tablePt K ((nafMagnitude b+1)/2)).z,
      6000+64*((nafMagnitude b+1)/2-1),6032+64*((nafMagnitude b+1)/2-1)],x∈V) :
    WP isa (.block lookupCode) s fun t =>
      ProgKeep K.M base entryWrites s t ∧
      Inv K.M base size C.p Sl (entryLive V) (tmv C K.M.n base t) t ∧
      (tmv C K.M.n base t K.E.x,tmv C K.M.n base t K.E.y,tmv C K.M.n base t K.E.z)=
        (E (Jacobian.tablePt K ((nafMagnitude b+1)/2)).x,
         E (Jacobian.tablePt K ((nafMagnitude b+1)/2)).y,E (Jacobian.tablePt K ((nafMagnitude b+1)/2)).z) ∧
      tmv C K.M.n base t 5400=E (6000+64*((nafMagnitude b+1)/2-1)) ∧
      tmv C K.M.n base t 5432=E (6032+64*((nafMagnitude b+1)/2-1)) := by
  rw [lookupCode,List.append_assoc,WP.block_append_iff]
  refine WP.mono (nafIndex_ok h2) fun u ⟨u2,ku⟩ => ?_
  refine WP.mono (entryLoadFields_ok hL hAl hsize (hi.of_keeps ku (by decide)) u2 ha ha8 hD hT)
    fun t ⟨kt,it,vt,v2,v3⟩ => ⟨?_,it,vt,v2,v3⟩
  exact (keeps_prog ku (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [clob])).trans kt

theorem lookup_relCT {base : Addr} {size : Nat} {b : BitVec 8} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hsize : 6512≤size)
    {V : List Nat} {E : Nat → Fe C}
    (ha : 1≤(nafMagnitude b+1)/2) (ha8 : (nafMagnitude b+1)/2≤8)
    (hD : ∀ x∈entryWrites,Sl x)
    (hT : ∀ x∈[(Jacobian.tablePt K ((nafMagnitude b+1)/2)).x,
      (Jacobian.tablePt K ((nafMagnitude b+1)/2)).y,(Jacobian.tablePt K ((nafMagnitude b+1)/2)).z,
      6000+64*((nafMagnitude b+1)/2-1),6032+64*((nafMagnitude b+1)/2-1)],x∈V)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x2])) (.block lookupCode)) :
    RelCT isa (fun s t => FieldPair K.M base size C.p Sl V E s t ∧
      s.gpr .x2=b.setWidth 64 ∧ t.gpr .x2=b.setWidth 64) (.block lookupCode)
      (fun s t => ∃ E',FieldPair K.M base size C.p Sl (entryLive V) E' s t) := by
  let a := (nafMagnitude b+1)/2
  let p := Jacobian.tablePt K a
  let F := fun x => if x=K.E.x then E p.x else if x=K.E.y then E p.y else if x=K.E.z then E p.z
    else if x=5400 then E (6000+64*(a-1)) else E (6032+64*(a-1))
  apply fieldWrite_relCT (F:=F) hL hct
  · intro s t hp ps pt
    refine ⟨hp.sp,fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
    · exact ps.trans pt.symm
  · exact hD
  · intro x hx
    simp only [entryLive,entryWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  · intro s hi hp
    refine WP.mono (lookupFields_ok hL hAl hsize hi hp ha ha8 hD hT) fun t ⟨hk,it,vt,v2,v3⟩ => ⟨_,hk,it,?_⟩
    intro x _ hx
    simp only [entryWrites,List.mem_cons,List.not_mem_nil,or_false] at hx
    simp only [Prod.mk.injEq] at vt
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · simpa only [F,ite_true] using vt.1
    · simpa only [F,show K.E.y≠K.E.x by decide,ite_false,ite_true] using vt.2.1
    · simpa only [F,show K.E.z≠K.E.x by decide,show K.E.z≠K.E.y by decide,ite_false,ite_true] using vt.2.2
    · simpa only [F,show 5400≠K.E.x by decide,show 5400≠K.E.y by decide,show 5400≠K.E.z by decide,ite_false,ite_true] using v2
    · simpa only [F,show 5432≠K.E.x by decide,show 5432≠K.E.y by decide,show 5432≠K.E.z by decide,
        show (5432:Nat)≠5400 by decide,ite_false] using v3

end VG.Proof.Weierstrass.AArch64.CachedField
