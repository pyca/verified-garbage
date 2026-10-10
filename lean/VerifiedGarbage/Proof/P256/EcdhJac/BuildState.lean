import VerifiedGarbage.Proof.P256.EcdhJac.StoreWords
import VerifiedGarbage.Proof.P256.EcdhJac.Frame
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd

/-! ## `Store` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.P256.EcdhJac (entryAddr storeEntry selectedWord)

theorem entryAddr_ok {base : Addr} {s : State} {m : Nat}
    (hs : s.gpr .x0=base) (hm : 1≤m) (h19 : s.gpr .x19=BitVec.ofNat 64 m) :
    WP isa (.block entryAddr) s fun t =>
      t.gpr .x16=off base (2816+160*(m-1)) ∧ Keeps [.x1,.x2,.x16] s t := by
  apply WP.of_runBlock
  simp only [entryAddr,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    show (1:Nat)<4096 by decide,show VG.Impl.P256.EcdhJac.K.tbl=2816 from rfl,
    show (2816:Nat)<4096 by decide,show 16*0<64 by decide,ite_true,
    RegUpd.gpr_write,BitVec.setWidth_eq,Size.bits,reduceCtorEq,ite_false,h19,hs,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.ofNat_sub_ofNat_of_le m 1 (by decide) hm]
    change base+BitVec.ofNat 64 2816+BitVec.ofNat 64 (m-1)*BitVec.ofNat 64 160=off base (2816+160*(m-1))
    rw [←BitVec.ofNat_mul]
    simp only [off,BitVec.ofNat_add,BitVec.add_assoc,Nat.mul_comm]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

/-- Store all five selected coordinates to the public construction index. -/
theorem storeEntry_ok {base : Addr} {s : State} {m : Nat}
    (hs : Scr s base 8192) (hm : 1≤m) (hm16 : m≤16)
    (h19 : s.gpr .x19=BitVec.ofNat 64 m) :
    WP isa (.block storeEntry) s fun t =>
      (∀i<20,word t.mem base (2816+160*(m-1)+8*i)=word s.mem base (selectedWord i)) ∧
      KeepRegs [.x1,.x2,.x16] s t ∧ Outside base (2816+160*(m-1)) 160 s.mem t.mem := by
  rw [storeEntry,WP.block_append_iff]
  refine WP.mono (entryAddr_ok hs.x0 hm h19) fun a ⟨pa,ka⟩ => ?_
  have ha := hs.of_keeps ka (by decide)
  refine WP.mono (tableStoreWords_ok (n:=20) ha pa (by omega)
    (by intro i hi; change (if i<12 then 704+8*i else 5400+8*(i-12))+8≤8192; split <;> omega)
    (by intro i hi; change (if i<12 then 704+8*i else 5400+8*(i-12))%8=0; split <;> omega)
    (by intro i hi; change 2816+160*(m-1)+8*20≤(if i<12 then 704+8*i else 5400+8*(i-12)) ∨ (if i<12 then 704+8*i else 5400+8*(i-12))+8≤2816+160*(m-1); split <;> omega) 20 (by omega)) fun t ⟨vals,kt,ot⟩ => ?_
  refine ⟨?_,(Keeps.regs ka).trans (kt.mono (by simp)),?_⟩
  · simpa only [ka.mem] using vals
  · simpa only [ka.mem] using ot


theorem storePoint_ok {base : Addr} {s : State} {m : Nat} {Q : Spec.Weierstrass.Point C}
    (hs : Scr s base 8192) (hm : 1≤m) (hm16 : m≤16)
    (h19 : s.gpr .x19=BitVec.ofNat 64 m) (hq : JPt base s selectedSlot Q) :
    WP isa (.block storeEntry) s fun t =>
      Frame base buildWork s t ∧ Outside base (2816+160*(m-1)) 160 s.mem t.mem ∧
      JPt base t (entrySlot m) Q ∧ t.gpr .x19=s.gpr .x19 := by
  refine WP.mono (storeEntry_ok hs hm hm16 h19) fun t ⟨hv,hk,ho⟩ => ⟨?_,ho,?_,hk.gpr _ (by decide)⟩
  · exact ⟨hk.mono (by decide),ho.unch.cover (by
      intro w hw; rw [List.mem_singleton.mp hw]
      exact ⟨(2816,2560),by simp [buildWork],by omega,by omega⟩)⟩
  · apply hq.congr
    intro c hc
    apply wordsVal_of_words₂
    intro i hi
    have h := hv (4*c+i) (by omega)
    have dst : 2816+160*(m-1)+8*(4*c+i)=entrySlot m c+8*i := by unfold entrySlot; omega
    have src : selectedWord (4*c+i)=selectedSlot c+8*i := by
      change (if 4*c+i<12 then 704+8*(4*c+i) else 5400+8*(4*c+i-12))=
        (if c<3 then 704+32*c else 5400+32*(c-3))+8*i
      split <;> split <;> omega
    simpa only [dst,src] using h

end VG.Proof.P256.EcdhJac

end

/-! ## `BuildInit` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open Spec.Weierstrass

 theorem opFrame {base : Addr} {s t : State} {o : Nat} (ho : o∈[608,640,704,736,768,5400,5432])
    (hk : OpKeep M base o s t) : Frame base work s t := by
  refine ⟨(⟨hk.gpr,hk.rd,hk.wr,hk.sp⟩ : KeepRegs (clob M.n) s t).mono clob_regs,?_⟩
  have h : Unch base [(o,32),(128,32)] s.mem t.mem := fun x hx => hk.mem x (hx (o,32) (by simp)) (hx (128,32) (by simp))
  exact h.cover ((show ∀o∈[608,640,704,736,768,5400,5432],∀w∈[(o,32),(128,32)],
    ∃w'∈work,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2 from by decide +kernel) o ho)

 theorem initialPoint_ok {base : Addr} {P : Point C} {k : Nat} {s : State}
    (hf : Fixed base P k s) :
    WP isa (.block (copyPt 4 K.E K.P++copy 4 5400 K.P.z++copy 4 5432 K.P.z)) s fun t =>
      Frame base work s t ∧ Fixed base P k t ∧ JPt base t selectedSlot P := by
  simp only [copyPt,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok layout aligned hf.field (o:=704) (a:=K.P.x) (by decide) (by decide))
    fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok layout aligned ia (o:=736) (a:=K.P.y) (by decide) (by decide))
    fun b ⟨kb,ib⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok layout aligned ib (o:=768) (a:=K.P.z) (by decide) (by decide))
    fun d ⟨kd,id⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok layout aligned id (o:=5400) (a:=K.P.z) (by decide) (by decide))
    fun e ⟨ke,ie⟩ => ?_
  refine WP.mono (copyField_ok layout aligned ie (o:=5432) (a:=K.P.z) (by decide) (by decide))
    fun t ⟨kt,it⟩ => ?_
  have fr := ((((opFrame (by decide) ka).trans (opFrame (by decide) kb)).trans
    (opFrame (by decide) kd)).trans (opFrame (by decide) ke)).trans (opFrame (by decide) kt)
  have one : tmv C 4 base s 224=1 := hf.one
  have hv : ∀i<5,tmv C 4 base t (selectedSlot i)=
      if i=0 then tmv C 4 base s K.P.x else if i=1 then tmv C 4 base s K.P.y else 1 := by
    intro i hi
    have he := it.val (selectedSlot i) (by
      have : i=0∨i=1∨i=2∨i=3∨i=4 := by omega
      rcases this with rfl|rfl|rfl|rfl|rfl <;> decide)
    change tmv C 4 base t (selectedSlot i)=_ at he
    have : i=0∨i=1∨i=2∨i=3∨i=4 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl <;>
      simpa only [selectedSlot,show K.P.x=1280 from rfl,show K.P.y=1440 from rfl,
        show K.P.z=224 from rfl,Function.update_apply,Nat.reduceLT,Nat.reduceAdd,Nat.reduceMul,
        Nat.reduceSub,Nat.reduceEqDiff,ite_true,ite_false,one] using he
  refine ⟨fr,hf.keep (frame_build fr),?_,?_,?_,?_,?_⟩
  · intro i hi
    apply it.lt
    have : i=0∨i=1∨i=2∨i=3∨i=4 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl <;> decide
  · rw [hv 0 (by decide),hv 1 (by decide),hv 2 (by decide)]
    simp only [Nat.reduceEqDiff,ite_true,ite_false]
    have hj := InvJ.of_rep01 hf.peer (Or.inl hf.one)
    rw [hf.one] at hj
    exact hj
  · rw [hv 2 (by decide)]
    exact (by decide : (1 : Fin C.p) ≠ 0)
  · simp only [hv 3 (by decide),hv 2 (by decide),Nat.reduceEqDiff,ite_false]
    grind
  · simp only [hv 4 (by decide),hv 3 (by decide),hv 2 (by decide),Nat.reduceEqDiff,ite_false]
    grind

end VG.Proof.P256.EcdhJac

end

/-! ## `BuildState` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

structure BuildInv (base : Addr) (P : Point C) (k m : Nat) (s : State) : Prop where
  fixed : Fixed base P k s
  table : TblOk base P m s
  selected : JPt base s selectedSlot (mul m P)
  counter : s.gpr .x19=BitVec.ofNat 64 m

structure CoZInv (base : Addr) (P : Point C) (k m : Nat) (s : State) : Prop where
  inv : BuildInv base P k m s
  lt : ∀x∈[K.D.x,K.D.y],wordsVal s.mem base x 4<C.p
  d : InvJ C (tmv C 4 base s K.D.x) (tmv C 4 base s K.D.y) (tmv C 4 base s K.E.z) P

theorem table_keep {base : Addr} {P : Point C} {n : Nat} {s t : State}
    (h : TblOk base P n s) (hn : n≤16) (hk : Frame base work s t) : TblOk base P n t := by
  intro a ha han
  apply (h a ha han).congr
  intro i hi
  exact hk.unch.wordsVal (by
    have hh : ∀a∈List.range 17,1≤a→∀i<5,∀w∈work,entrySlot a i+32≤w.1 ∨ w.1+w.2≤entrySlot a i := by decide +kernel
    exact hh a (List.mem_range.mpr (by omega)) ha i hi) (by unfold entrySlot; omega)

theorem table_store {base : Addr} {P : Point C} {m : Nat} {s t : State}
    (h : TblOk base P m s) (hm : m<16)
    (ho : Outside base (2816+160*m) 160 s.mem t.mem) : TblOk base P m t := by
  intro a ha ham
  apply (h a ha ham).congr
  intro i hi
  exact ho.wordsVal (by unfold entrySlot; omega) (by unfold entrySlot; omega)

theorem selected_store {base : Addr} {Q : Point C} {m : Nat} {s t : State}
    (h : JPt base s selectedSlot Q) (hm : 1≤m) (hm16 : m≤16)
    (ho : Outside base (2816+160*(m-1)) 160 s.mem t.mem) : JPt base t selectedSlot Q := by
  apply h.congr
  intro i hi
  apply ho.wordsVal
  · unfold selectedSlot; split <;> omega
  · unfold selectedSlot; split <;> omega

 theorem selected_keeps {base : Addr} {Q : Point C} {s t : State} {rs : List Reg}
    (h : JPt base s selectedSlot Q) (hk : VG.Proof.Ed25519.AArch64.Keeps rs s t) :
    JPt base t selectedSlot Q := h.congr (fun _ _ => by rw [hk.mem])

end VG.Proof.P256.EcdhJac

end
