module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Initial
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitialOneTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure InitialReadyW (w16 : Bool) (A B : Nat→Byte) (a b : Nat) (s : State) : Prop where
 left : OneReadyW w16 A 400 a 1680 s
 right : OneReadyW w16 B 904 b 1696 s
 far : (polyRegion (s.gpr .x28+BitVec.ofNat 64 a)).Disjoint ⟨s.gpr .x19,2048⟩
 table : ∀mask<256,(Region.mk (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16).Disjoint ⟨s.gpr .x19,2048⟩

theorem InitialReadyW.afterLeft {w16 : Bool} {s t : State} {A B : Nat→Byte} {a b : Nat}
 (h : InitialReadyW w16 A B a b s)
 (ht : InitialOnePostW w16 A (s.gpr .x28+BitVec.ofNat 64 a) (s.gpr .x19+BitVec.ofNat 64 1680) .x22 s t) :
 OneReadyW w16 B 904 b 1696 t := by
 have t19 := ht.keep.get .x19 (by decide)
 have t28 := ht.keep.get .x28 (by decide)
 have t16 := ht.keep.get .x16 (by decide)
 refine ⟨?_,ht.constants,?_,?_,?_⟩
 · rw [t19,t28]
   refine h.right.env.frame ht.keep.rd ht.keep.wr t16 ht.frame ?_ ?_
   · intro r hr
     simp only [initialWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl
     · exact (h.far.sub_right (Offset.sub_base _ (by decide))).symm
     · exact Offset.disjoint (s.gpr .x19) (d:=904) (n:=508) (e:=1680) (k:=16) (by decide) (by decide) (by decide)
   · intro mask hm r hr
     simp only [initialWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl
     · exact h.left.env.tableDisj mask hm
     · exact (h.table mask hm).sub_right (Offset.sub_base _ (by decide))
 · simpa only [ht.keep.wr,t19] using h.right.out0
 · simpa only [ht.keep.wr,t19] using h.right.out1
 · simpa only [t19,t28] using h.right.apart

theorem initial_relCT {w16 : Bool} {s u : State} {A B : Nat→Byte} {a b : Nat}
 (ha : a<65536) (hb : b<65536) (hs : InitialReadyW w16 A B a b s) (hu : InitialReadyW w16 A B a b u)
 (sp : s.sp=u.sp) (h19 : s.gpr .x19=u.gpr .x19) (h28 : s.gpr .x28=u.gpr .x28)
 (h16 : s.gpr .x16=u.gpr .x16) :
 RelCT isa (fun x y=>x=s ∧ y=u) (initialCode a b w16) (fun _ _=>True) := by
 apply RelCT.assoc
 refine RelCT.seq (initialOne_relCT (by decide) ha (by decide) (by decide) (by decide)
   hs.left hu.left sp h19 h28 h16) ?_
 intro x y tx ty x' y' h ex ey
 have px := hs.afterLeft h.1
 have py := hu.afterLeft h.2
 have sx : x.sp=y.sp := h.1.keep.sp.trans (sp.trans h.2.keep.sp.symm)
 have e19 : x.gpr .x19=y.gpr .x19 := by rw [h.1.keep.get .x19,h.2.keep.get .x19,h19]
 have e28 : x.gpr .x28=y.gpr .x28 := by rw [h.1.keep.get .x28,h.2.keep.get .x28,h28]
 have e16 : x.gpr .x16=y.gpr .x16 := by rw [h.1.keep.get .x16,h.2.keep.get .x16,h16]
 have rest : RelCT isa (fun v w=>v=x ∧ w=y)
     (.seq (initialOne 904 b 1696 .x23 w16) (.block [.logic .and .x .x6 .x22 .x23])) (fun _ _=>True) := by
  refine RelCT.seq (initialOne_relCT (by decide) hb (by decide) (by decide) (by decide) px py sx e19 e28 e16) ?_
  intro v w vt wt v' w' hw ev ew
  have ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
      (.block [.logic .and .x .x6 .x22 .x23]) :=
    VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl
  exact ⟨ct v w vt wt v' w' trivial trivial
    (agree_of (hw.1.keep.sp.trans (sx.trans hw.2.keep.sp.symm)) (by simp)) ev ew,trivial⟩
 exact RelCT.assoc rest x y tx ty x' y' ⟨rfl,rfl⟩ ex ey
end VG.Proof.MlKem.AArch64.Paired
