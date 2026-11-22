module

public import VerifiedGarbage.Proof.P256.EcdhJac.DbluCertificate
public import VerifiedGarbage.Proof.P256.EcdhTable.Dblu
public import VerifiedGarbage.Proof.P256.EcdhTable.Zaddu
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.P256.EcdhTable.Transfer
import VerifiedGarbage.Proof.P256.EcdhJac.Frame
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.P256.EcdhJac.State
import VerifiedGarbage.Proof.P256.EcdhJac.StoreWords
import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-! ### `P256.EcdhJac.BuildState`, which this module and modules that import it used -/

section

/-! ## `Store` -/

@[expose] public section

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
  refine WP.mono (tableStoreWords_ok (n:=20) ha pa (by omega_arith)
    (by intro i hi; change (if i<12 then 704+8*i else 5400+8*(i-12))+8≤8192; split <;> omega_arith)
    (by intro i hi; change (if i<12 then 704+8*i else 5400+8*(i-12))%8=0; split <;> omega_arith)
    (by intro i hi; change 2816+160*(m-1)+8*20≤(if i<12 then 704+8*i else 5400+8*(i-12)) ∨ (if i<12 then 704+8*i else 5400+8*(i-12))+8≤2816+160*(m-1); split <;> omega_arith) 20 (by omega_arith)) fun t ⟨vals,kt,ot⟩ => ?_
  refine ⟨?_,(Keeps.regs ka).trans (kt.mono (by regions_sub)),?_⟩
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
      exact ⟨(2816,2560),by simp [buildWork],by omega_arith,by omega_arith⟩)⟩
  · apply hq.congr
    intro c hc
    apply wordsVal_of_words₂
    intro i hi
    have h := hv (4*c+i) (by omega_arith)
    have dst : 2816+160*(m-1)+8*(4*c+i)=entrySlot m c+8*i := by unfold entrySlot; omega_arith
    have src : selectedWord (4*c+i)=selectedSlot c+8*i := by
      change (if 4*c+i<12 then 704+8*(4*c+i) else 5400+8*(4*c+i-12))=
        (if c<3 then 704+32*c else 5400+32*(c-3))+8*i
      split <;> split <;> omega_arith
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
      have : i=0∨i=1∨i=2∨i=3∨i=4 := by omega_arith
      rcases this with rfl|rfl|rfl|rfl|rfl <;> decide)
    change tmv C 4 base t (selectedSlot i)=_ at he
    have : i=0∨i=1∨i=2∨i=3∨i=4 := by omega_arith
    rcases this with rfl|rfl|rfl|rfl|rfl <;>
      simpa only [selectedSlot,show K.P.x=1280 from rfl,show K.P.y=1440 from rfl,
        show K.P.z=224 from rfl,Function.update_apply,Nat.reduceLT,Nat.reduceAdd,Nat.reduceMul,
        Nat.reduceSub,Nat.reduceEqDiff,ite_true,ite_false,one] using he
  refine ⟨fr,hf.keep (frame_build fr),?_,?_,?_,?_,?_⟩
  · intro i hi
    apply it.lt
    have : i=0∨i=1∨i=2∨i=3∨i=4 := by omega_arith
    rcases this with rfl|rfl|rfl|rfl|rfl <;> decide
  · rw [hv 0 (by decide),hv 1 (by decide),hv 2 (by decide)]
    simp only [Nat.reduceEqDiff,ite_true,ite_false]
    have hj := InvJ.of_rep01 hf.peer (Or.inl hf.one)
    rw [hf.one] at hj
    exact hj
  · rw [hv 2 (by decide)]
    exact (by decide : (1 : Fin C.p) ≠ 0)
  · simp only [hv 3 (by decide),hv 2 (by decide),Nat.reduceEqDiff,ite_false]
    -- `-lia`: Lean 4.36's `grind` builds a proof the kernel rejects from `lia`
    -- over `Fin` of a non-literal modulus (lean4#15857, fixed in 4.37).
    grind -lia
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
    exact hh a (List.mem_range.mpr (by omega_arith)) ha i hi) (by unfold entrySlot; omega_arith)

theorem table_store {base : Addr} {P : Point C} {m : Nat} {s t : State}
    (h : TblOk base P m s) (hm : m<16)
    (ho : Outside base (2816+160*m) 160 s.mem t.mem) : TblOk base P m t := by
  intro a ha ham
  apply (h a ha ham).congr
  intro i hi
  exact ho.wordsVal (by unfold entrySlot; omega_arith) (by unfold entrySlot; omega_arith)

theorem selected_store {base : Addr} {Q : Point C} {m : Nat} {s t : State}
    (h : JPt base s selectedSlot Q) (hm : 1≤m) (hm16 : m≤16)
    (ho : Outside base (2816+160*(m-1)) 160 s.mem t.mem) : JPt base t selectedSlot Q := by
  apply h.congr
  intro i hi
  apply ho.wordsVal
  · unfold selectedSlot; split <;> omega_arith
  · unfold selectedSlot; split <;> omega_arith

 theorem selected_keeps {base : Addr} {Q : Point C} {s t : State} {rs : List Reg}
    (h : JPt base s selectedSlot Q) (hk : VG.Proof.Ed25519.AArch64.Keeps rs s t) :
    JPt base t selectedSlot Q := h.congr (fun _ _ => by rw [hk.mem])

end VG.Proof.P256.EcdhJac

end

end

end

/-! ## `BuildStart` -/

@[expose] public section

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
    have : m=1 := by omega_using [hm, hm1]
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
      (by unfold selectedSlot; split <;> omega_using [hi])
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
  have old := table_store ht (by omega_using [hm16]) ot
  have selected := selected_store hp hm hm16 ot
  have hv : ∀x∈[K.D.x,K.D.y,K.E.z],wordsVal t.mem base x 4=wordsVal s.mem base x 4 := by
    intro x hx
    exact ot.wordsVal (by
      have h : x=608∨x=640∨x=768 := by
        simpa only [show K.D.x=608 from rfl,show K.D.y=640 from rfl,show K.E.z=768 from rfl,List.mem_cons,List.not_mem_nil,or_false] using hx
      rcases h with rfl|rfl|rfl <;> omega_using []) (by
      have h : x=608∨x=640∨x=768 := by
        simpa only [show K.D.x=608 from rfl,show K.D.y=640 from rfl,show K.E.z=768 from rfl,List.mem_cons,List.not_mem_nil,or_false] using hx
      rcases h with rfl|rfl|rfl <;> omega_using [])
  refine ⟨kt,⟨⟨hf.keep kt,?_,selected,ct.trans h19⟩,?_,?_⟩⟩
  · intro a ha ham
    by_cases h : a=m
    · subst a; exact pt
    · exact old a ha (by omega_using [ham, h])
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
