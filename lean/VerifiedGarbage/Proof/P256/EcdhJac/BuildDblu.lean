import VerifiedGarbage.Proof.P256.EcdhJac.BuildState
import VerifiedGarbage.Proof.P256.EcdhTable.Transfer

/-! ## `BuildStart` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open Spec.Weierstrass

 theorem movCounter_ok (s : State) (n : BitVec 16) :
    WP isa (.block [.movz .x .x19 n 0]) s fun t => t.gpr .x19=n.setWidth 64 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,Size.bits,
    show 16*0<64 by decide,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  · simp
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

 theorem buildStart_ok {base : Addr} {P : Point C} {k : Nat} {s : State} (hf : Fixed base P k s) :
    WP isa (.block (copyPt 4 K.E K.P++copy 4 5400 K.P.z++copy 4 5432 K.P.z++
      [.movz .x .x19 1 0]++Impl.P256.EcdhJac.storeEntry)) s fun t =>
      Frame base buildWork s t ∧ BuildInv base P k 1 t := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (initialPoint_ok hf) fun a ⟨ka,fa,pa⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movCounter_ok a 1) fun b ⟨cb,kb⟩ => ?_
  have fb := fa.keep (frame_build ((AllocatedFrame.of_keeps kb).widenRegs (by decide)))
  have pb := selected_keeps pa kb
  refine WP.mono (storePoint_ok (m:=1) fb.field.scr (by decide) (by decide) cb pb) fun t ⟨kt,ot,pt,ct⟩ => ?_
  have pb' := selected_store (m:=1) pb (by decide) (by decide) ot
  have fr := (frame_build ka).trans
    (((AllocatedFrame.of_keeps kb).widenRegs (by decide)).trans kt)
  refine ⟨fr,⟨fb.keep kt,?_,?_,ct.trans cb⟩⟩
  · intro m hm hm1
    have : m=1 := by omega
    subst m
    simpa only [mul_one_pt] using pt
  · simpa only [mul_one_pt] using pb'

end VG.Proof.P256.EcdhJac

end

/-! ## `CopyD` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem copyD_ok {base : Addr} {P Q : Point C} {k : Nat} {s : State}
    (hf : Fixed base P k s) (hp : JPt base s selectedSlot Q)
    (hd : InvJ C (tmv C 4 base s K.S.t3) (tmv C 4 base s K.S.t2) (tmv C 4 base s K.E.z) P)
    (hx : wordsVal s.mem base K.S.t3 4<C.p) (hy : wordsVal s.mem base K.S.t2 4<C.p) :
    WP isa (.block (copy 4 K.D.x K.S.t3++copy 4 K.D.y K.S.t2)) s fun t =>
      Frame base work s t ∧ JPt base t selectedSlot Q ∧
      (∀x∈[K.D.x,K.D.y],wordsVal t.mem base x 4<C.p) ∧
      InvJ C (tmv C 4 base t K.D.x) (tmv C 4 base t K.D.y) (tmv C 4 base t K.E.z) P := by
  have hi : Inv M base 8192 C.p Sl [K.S.t3,K.S.t2] (tmv C 4 base s) s :=
    ⟨hf.field.scr,hf.field.mod,by decide,fun x hh => by
      rcases List.mem_cons.mp hh with rfl|hh
      · exact hx
      · rw [List.mem_singleton.mp hh]; exact hy,fun _ _ => rfl⟩
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok layout aligned hi (o:=K.D.x) (a:=K.S.t3) (by decide) (by decide))
    fun a ⟨ka,ia⟩ => ?_
  refine WP.mono (copyField_ok layout aligned ia (o:=K.D.y) (a:=K.S.t2) (by decide) (by decide))
    fun t ⟨kt,it⟩ => ?_
  have fr := (opFrame (by decide) ka).trans (opFrame (by decide) kt)
  have un : Unch base [(608,32),(640,32),(128,32)] s.mem t.mem := by
    intro x hh
    exact (kt.mem x (hh (640,32) (by simp)) (hh (128,32) (by simp))).trans
      (ka.mem x (hh (608,32) (by simp)) (hh (128,32) (by simp)))
  have sel : ∀i<5,wordsVal t.mem base (selectedSlot i) 4=wordsVal s.mem base (selectedSlot i) 4 := by
    intro i hi
    exact un.wordsVal ((show ∀i<5,∀w∈[(608,32),(640,32),(128,32)],selectedSlot i+32≤w.1 ∨ w.1+w.2≤selectedSlot i from by decide +kernel) i hi)
      (by unfold selectedSlot; split <;> omega)
  have vx := it.val K.D.x (by decide)
  have vy := it.val K.D.y (by decide)
  change tmv C 4 base t 608=_ at vx
  change tmv C 4 base t 640=_ at vy
  simp only [show K.D.x=608 from rfl,show K.D.y=640 from rfl,
    show K.S.t3=896 from rfl,show K.S.t2=864 from rfl,
    Function.update_apply,Nat.reduceEqDiff,ite_true,ite_false] at vx vy
  refine ⟨fr,hp.congr sel,fun x hh => it.lt x ?_,?_⟩
  · rcases List.mem_cons.mp hh with rfl|hh
    · decide
    · rw [List.mem_singleton.mp hh]; decide
  · change InvJ C (tmv C 4 base t 608) (tmv C 4 base t 640) (tmv C 4 base t 768) P
    have vz : tmv C 4 base t 768=tmv C 4 base s 768 := by
      simpa only [selectedSlot,show 2<3 from by decide,ite_true,Nat.reduceMul,Nat.reduceAdd]
        using congrArg (fun x => toM C.p (2^(64*4)) x) (sel 2 (by decide))
    rw [vx,vy,vz]
    exact hd

end VG.Proof.P256.EcdhJac

end

/-! ## `BuildStore` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

 theorem storeCoZ_ok {base : Addr} {P : Point C} {k m : Nat} {s : State}
    (hm : 1≤m) (hm16 : m≤16) (hf : Fixed base P k s)
    (ht : TblOk base P (m-1) s) (hp : JPt base s selectedSlot (mul m P))
    (hl : ∀x∈[K.D.x,K.D.y],wordsVal s.mem base x 4<C.p)
    (hd : InvJ C (tmv C 4 base s K.D.x) (tmv C 4 base s K.D.y) (tmv C 4 base s K.E.z) P)
    (h19 : s.gpr .x19=BitVec.ofNat 64 m) :
    WP isa (.block Impl.P256.EcdhJac.storeEntry) s fun t =>
      Frame base buildWork s t ∧ CoZInv base P k m t := by
  refine WP.mono (storePoint_ok hf.field.scr hm hm16 h19 hp) fun t ⟨kt,ot,pt,ct⟩ => ?_
  have old := table_store ht (by omega) ot
  have selected := selected_store hp hm hm16 ot
  have hv : ∀x∈[K.D.x,K.D.y,K.E.z],wordsVal t.mem base x 4=wordsVal s.mem base x 4 := by
    intro x hx
    exact ot.wordsVal (by
      have h : x=608∨x=640∨x=768 := by
        simpa only [show K.D.x=608 from rfl,show K.D.y=640 from rfl,show K.E.z=768 from rfl,List.mem_cons,List.not_mem_nil,or_false] using hx
      rcases h with rfl|rfl|rfl <;> omega) (by
      have h : x=608∨x=640∨x=768 := by
        simpa only [show K.D.x=608 from rfl,show K.D.y=640 from rfl,show K.E.z=768 from rfl,List.mem_cons,List.not_mem_nil,or_false] using hx
      rcases h with rfl|rfl|rfl <;> omega)
  refine ⟨kt,⟨⟨hf.keep kt,?_,selected,ct.trans h19⟩,?_,?_⟩⟩
  · intro a ha ham
    by_cases h : a=m
    · subst a; exact pt
    · exact old a ha (by omega)
  · intro x hx
    rw [hv x (by
      rcases List.mem_cons.mp hx with rfl|hx
      · decide
      · rw [List.mem_singleton.mp hx]; decide)]
    exact hl x hx
  · have vx := congrArg (fun x => toM C.p (2^256) x) (hv K.D.x (by decide))
    have vy := congrArg (fun x => toM C.p (2^256) x) (hv K.D.y (by decide))
    have vz := congrArg (fun x => toM C.p (2^256) x) (hv K.E.z (by decide))
    change tmv C 4 base t K.D.x=tmv C 4 base s K.D.x at vx
    change tmv C 4 base t K.D.y=tmv C 4 base s K.D.y at vy
    change tmv C 4 base t K.E.z=tmv C 4 base s K.E.z at vz
    rw [vx,vy,vz]
    exact hd

end VG.Proof.P256.EcdhJac

end

/-! ## `BuildDblu` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem buildDblu_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k : Nat} {s : State} (hP : onCurve C P=true)
    (hi : BuildInv base P k 1 s) :
    WP isa (.seq (Impl.P256.EcdhTable.program true)
      (.block (copy 4 K.D.x K.S.t3++copy 4 K.D.y K.S.t2++
        ([.movz .x .x19 2 0] : List Instr)++Impl.P256.EcdhJac.storeEntry))) s fun t =>
      Frame base buildWork s t ∧ CoZInv base P k 2 t := by
  refine WP.seq (WP.mono (EcdhTable.dblu_ok hC ha hO hP hi.fixed) fun a ⟨ka,fa,pa,da,xa,ya⟩ => ?_)
  have ta := table_keep hi.table (by decide) ka
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (copyD_ok fa pa da xa ya) fun b ⟨kb,pb,lb,db⟩ => ?_
  have fb := fa.keep (frame_build kb)
  have tb := table_keep ta (by decide) kb
  rw [WP.block_append_iff]
  refine WP.mono (movCounter_ok b 2) fun d ⟨cd,kd⟩ => ?_
  have fd := fb.keep (frame_build ((AllocatedFrame.of_keeps kd).widenRegs (by decide)))
  have td : TblOk base P 1 d := by
    intro m hm hm1
    apply (tb m hm hm1).congr
    intro i hi
    rw [kd.mem]
  have pd := selected_keeps pb kd
  have ld : ∀x∈[K.D.x,K.D.y],wordsVal d.mem base x 4<C.p := by simpa only [kd.mem] using lb
  have dd : InvJ C (tmv C 4 base d K.D.x) (tmv C 4 base d K.D.y) (tmv C 4 base d K.E.z) P := by
    simpa only [tmv,kd.mem] using db
  refine WP.mono (storeCoZ_ok (m:=2) (by decide) (by decide) fd td pd ld dd cd) fun t ⟨kt,it⟩ =>
    ⟨(frame_build (ka.trans kb)).trans (((AllocatedFrame.of_keeps kd).widenRegs (by decide)).trans kt),it⟩

end VG.Proof.P256.EcdhJac

end
