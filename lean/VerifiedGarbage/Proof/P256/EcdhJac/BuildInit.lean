import VerifiedGarbage.Proof.P256.EcdhJac.Store
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd

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
