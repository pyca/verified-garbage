module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraBoth
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Keep
import VerifiedGarbage.Proof.Framework.Offset
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure BothReadyW (w16 : Bool) (L M : List Zq) (A B : Nat→Byte) (p a b : Addr) (s : State) : Prop where
 pointer : s.gpr .x19=p
 scratch : Covers [⟨p,2048⟩] s.wr
 farA : (Region.mk p 2048).Disjoint (polyRegion a)
 farB : (Region.mk p 2048).Disjoint (polyRegion b)
 apart : (polyRegion a).Disjoint (polyRegion b)
 left : ExtraReadyW w16 L A 400 1680 a s
 right : ExtraReadyW w16 M B 904 1696 b s
 table : ∀mask<256,(Region.mk (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16).Disjoint ⟨p,2048⟩

theorem BothReadyW.afterLeft {w16 : Bool} {s t : State} {L M : List Zq} {A B : Nat→Byte} {p a b : Addr}
 (h : BothReadyW w16 L M A B p a b s)
 (ht : ExtraPostW w16 L A a (s.gpr .x19+1680) .x22 s t) (cs : Rej8.Constants t) : ExtraReadyW w16 M B 904 1696 b t := by
 have tp : t.gpr .x19=p := (ht.keep.get .x19).trans h.pointer
 have hf : Frame [polyRegion a,⟨p+1680,16⟩] s.mem t.mem := by simpa only [h.pointer] using ht.frame
 refine ⟨?_,cs,h.right.len,?_,?_,?_,?_,?_⟩
 · rw [tp]
   apply (show Rej8.EnvW w16 56 B (p+BitVec.ofNat 64 904) b s by simpa only [h.pointer] using h.right.env).frame
     ht.keep.rd ht.keep.wr (ht.keep.get .x16) hf
   · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl
     · exact h.farA.sub_left (Offset.sub_base p (by decide))
     · exact Offset.disjoint p (by decide) (by decide) (by decide)
   · intro mask hm r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl
     · exact h.left.env.tableDisj mask hm
     · exact (h.table mask hm).sub_right (Offset.sub_base p (by decide))
 · exact coeffs_frame h.right.coeffs h.right.len hf (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.apart.symm
    · exact h.farB.symm.sub_right (Offset.sub_base p (by decide)))
 · rw [tp]
   exact checkpoint_frame (by simpa only [h.pointer] using h.right.saved) hf (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.farA.sub_left (Offset.sub_base p (by decide))
    · exact Offset.disjoint p (by decide) (by decide) (by decide))
 · simpa only [ht.keep.wr,ht.keep.get .x19] using h.right.out0
 · simpa only [ht.keep.wr,ht.keep.get .x19] using h.right.out1
 · simpa only [ht.keep.get .x19] using h.right.apart

theorem extraBoth_relCT {w16 : Bool} {s u : State} {L M : List Zq} {A B : Nat→Byte} {p a b : Addr}
 (hs : BothReadyW w16 L M A B p a b s) (hu : BothReadyW w16 L M A B p a b u)
 (sp : s.sp=u.sp) (table : s.gpr .x16=u.gpr .x16) :
 RelCT isa (fun x y=>x=s ∧ y=u) (extraBoth w16) (fun _ _=>True) := by
 have h19 : s.gpr .x19=u.gpr .x19 := hs.pointer.trans hu.pointer.symm
 have first : RelCT isa (fun x y=>x=s ∧ y=u)
     (Impl.MlKem.AArch64.Paired.extraReject 400 1680 .x22 w16)
     (fun x y=> (ExtraPostW w16 L A a (s.gpr .x19+1680) .x22 s x ∧ Rej8.Constants x) ∧
       (ExtraPostW w16 L A a (u.gpr .x19+1680) .x22 u y ∧ Rej8.Constants y)) := by
  intro x y tx ty x' y' h ex ey
  rcases h with ⟨hx,hy⟩
  subst x; subst y
  have result := extra_relCT (flag:=.x22) (by decide) (by decide) (by decide) (by decide) hs.left hu.left sp h19 table s u tx ty x' y' ⟨rfl,rfl⟩ ex ey
  have cx := exec_post (Rej8.WP.constants (extra_ok s (by decide) (by decide) (by decide) (by decide)
    hs.left.env hs.left.constants hs.left.len hs.left.coeffs hs.left.saved hs.left.out0 hs.left.out1 hs.left.apart)
    hs.left.constants (by cases w16 <;> rfl)) ex
  have cy := exec_post (Rej8.WP.constants (extra_ok u (by decide) (by decide) (by decide) (by decide)
    hu.left.env hu.left.constants hu.left.len hu.left.coeffs hu.left.saved hu.left.out0 hu.left.out1 hu.left.apart)
    hu.left.constants (by cases w16 <;> rfl)) ey
  exact ⟨result.1,⟨result.2.1,cx.2⟩,⟨result.2.2,cy.2⟩⟩
 refine RelCT.seq first ?_
 intro x y tx ty x' y' h ex ey
 have px := hs.afterLeft h.1.1 h.1.2
 have py := hu.afterLeft h.2.1 h.2.2
 have sx : x.sp=y.sp := h.1.1.keep.sp.trans (sp.trans h.2.1.keep.sp.symm)
 have tx16 : x.gpr .x16=y.gpr .x16 := by rw [h.1.1.keep.get .x16,h.2.1.keep.get .x16,table]
 have tx19 : x.gpr .x19=y.gpr .x19 := by rw [h.1.1.keep.get .x19,h.2.1.keep.get .x19,h19]
 have rest : RelCT isa (fun a b=>a=x ∧ b=y)
     (.seq (Impl.MlKem.AArch64.Paired.extraReject 904 1696 .x23 w16)
       (.block [.logic .and .x .x6 .x22 .x23])) (fun _ _=>True) := by
  refine RelCT.seq (extra_relCT (by decide) (by decide) (by decide) (by decide) px py sx tx19 tx16) ?_
  intro v w vt wt v' w' hw ev ew
  have ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [.logic .and .x .x6 .x22 .x23]) := by
      exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl
  exact ⟨ct v w vt wt v' w' trivial trivial
    (agree_of (hw.1.keep.sp.trans (sx.trans hw.2.keep.sp.symm)) (by simp)) ev ew,trivial⟩
 exact rest x y tx ty x' y' ⟨rfl,rfl⟩ ex ey
end VG.Proof.MlKem.AArch64.Paired
